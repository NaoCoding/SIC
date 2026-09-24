(() => {
  'use strict';

  const sample = ``;

  const ops = new Set(['LDA', 'LDX', 'STA', 'STX', 'ADD', 'SUB', 'MUL', 'DIV', 'COMP', 'J', 'JEQ', 'JGT', 'JLT', 'JSUB', 'RSUB', 'TIX']);
  const directives = new Set(['START', 'END', 'WORD', 'RESW']);
  const editor = document.getElementById('sourceEditor');
  const gutter = document.getElementById('lineNumbers');
  const registerGrid = document.getElementById('registerGrid');
  const memoryRows = document.getElementById('memoryRows');
  const traceList = document.getElementById('traceList');
  const memorySearch = document.getElementById('memorySearch');
  const runButton = document.getElementById('runButton');
  const notification = document.getElementById('notification');
  const RENDER_REGS = [['A', 'Accumulator'], ['X', 'Index'], ['L', 'Link'], ['PC', 'Program counter'], ['SW', 'Status word']];
  const state = {
    compiled: null, machine: null, timer: null, history: [], touched: new Set(),
    dirty: false, notificationTimer: null, lastRegisterValues: {},
  };

  const escapeHtml = (value) => String(value).replace(/[&<>"']/g, char => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[char]);
  const hex = (value, width = 6) => (Number(value) >>> 0).toString(16).toUpperCase().padStart(width, '0').slice(-width);
  const word = value => {
    const raw = Math.trunc(Number(value)) & 0xFFFFFF;
    return raw & 0x800000 ? raw - 0x1000000 : raw;
  };
  const numeric = value => {
    const clean = String(value ?? '').trim();
    if (/^[-+]?\d+$/.test(clean)) return Number(clean);
    if (/^0x[\da-f]+$/i.test(clean)) return parseInt(clean.slice(2), 16);
    if (/^[\da-f]+H$/i.test(clean)) return parseInt(clean.slice(0, -1), 16);
    return null;
  };
  const setNotification = message => {
    notification.textContent = message;
    notification.classList.add('show');
    clearTimeout(state.notificationTimer);
    state.notificationTimer = setTimeout(() => notification.classList.remove('show'), 3600);
  };
  const addLog = (message, tone = 'info') => {
    const now = new Date();
    state.history.unshift({ kind: 'log', message, tone, time: `${String(now.getHours()).padStart(2, '0')}:${String(now.getMinutes()).padStart(2, '0')}:${String(now.getSeconds()).padStart(2, '0')}` });
    state.history = state.history.slice(0, 70);
    renderTrace();
  };

  function assemble(source) {
    const errors = [];
    const labels = new Map();
    const statements = [];
    const image = new Map();
    const dataSymbols = [];
    const instructionMap = new Map();
    let loc = 0;
    let startAddress = 0;
    let endEntry = '';
    let pendingLabel = null;
    const lines = source.replace(/\r/g, '').split('\n');

    lines.forEach((raw, index) => {
      const trimmed = raw.trim();
      if (!trimmed || trimmed.startsWith('.') || trimmed.startsWith('```')) return;
      const tokens = trimmed.split(/[\s,]+/).filter(Boolean);
      if (!tokens.length) return;
      const first = tokens[0].toUpperCase();
      let label = '';
      let op;
      let operand = '';
      if (ops.has(first) || directives.has(first)) {
        op = first;
        operand = trimmed.slice(tokens[0].length).trim();
      } else {
        label = tokens[0].toUpperCase();
        if (tokens.length === 1) {
          if (pendingLabel) errors.push(`Line ${index + 1}: label ${pendingLabel.name} has no instruction.`);
          pendingLabel = { name: label, line: index + 1 };
          return;
        }
        const second = tokens[1].toUpperCase();
        if (!ops.has(second) && !directives.has(second)) {
          errors.push(`Line ${index + 1}: unknown operation “${tokens[1]}”.`);
          return;
        }
        op = second;
        const afterLabel = trimmed.slice(tokens[0].length).trim();
        const operationEnd = afterLabel.search(/\s/);
        operand = operationEnd < 0 ? '' : afterLabel.slice(operationEnd).trim();
      }
      if (!label && pendingLabel) { label = pendingLabel.name; pendingLabel = null; }
      if (label) {
        if (labels.has(label)) errors.push(`Line ${index + 1}: duplicate label ${label}.`);
        else labels.set(label, loc);
      }
      const statement = { line: index + 1, source: raw, label, op, operand, address: loc };
      statements.push(statement);
      if (op === 'START') {
        const origin = numeric(operand);
        if (origin === null) errors.push(`Line ${index + 1}: START requires a numeric address.`);
        else { loc = origin; startAddress = origin; statement.address = origin; if (label) labels.set(label, origin); }
      } else if (op === 'END') {
        endEntry = operand.trim().toUpperCase();
      } else if (op === 'WORD') {
        const value = numeric(operand);
        if (value === null) errors.push(`Line ${index + 1}: WORD requires an integer value.`);
        image.set(loc, word(value ?? 0));
        if (label) dataSymbols.push({ name: label, address: loc, kind: 'WORD', count: 1, line: index + 1 });
        loc += 3;
      } else if (op === 'RESW') {
        const count = numeric(operand);
        if (count === null || count < 0 || count > 65536) errors.push(`Line ${index + 1}: RESW requires a word count from 0 to 65536.`);
        const safeCount = Math.max(0, Math.min(65536, count ?? 0));
        for (let i = 0; i < safeCount; i++) image.set(loc + i * 3, 0);
        if (label) dataSymbols.push({ name: label, address: loc, kind: 'RESW', count: safeCount, line: index + 1 });
        loc += safeCount * 3;
      } else if (ops.has(op)) {
        instructionMap.set(loc, statement);
        loc += 3;
      }
    });
    if (pendingLabel) errors.push(`Line ${pendingLabel.line}: label ${pendingLabel.name} has no instruction.`);

    const needsOperand = new Set(['LDA', 'LDX', 'STA', 'STX', 'ADD', 'SUB', 'MUL', 'DIV', 'COMP', 'J', 'JEQ', 'JGT', 'JLT', 'JSUB', 'TIX']);
    for (const statement of statements) {
      if (ops.has(statement.op) && needsOperand.has(statement.op) && !statement.operand) errors.push(`Line ${statement.line}: ${statement.op} requires an operand.`);
      if (ops.has(statement.op) && statement.operand) {
        const name = statement.operand.replace(/^#/, '').replace(/,\s*X$/i, '').trim().toUpperCase();
        if (numeric(name) === null && !labels.has(name)) errors.push(`Line ${statement.line}: unknown symbol ${name}.`);
      }
    }
    if (!instructionMap.size) errors.push('No executable instructions were found.');
    const entryName = endEntry && numeric(endEntry) === null ? endEntry : '';
    const entryAddress = entryName ? labels.get(entryName) : (numeric(endEntry) ?? startAddress);
    const actualEntry = instructionMap.has(entryAddress) ? entryAddress : [...instructionMap.keys()].sort((a, b) => a - b)[0];
    if (entryName && !labels.has(entryName)) errors.push(`END refers to unknown entry symbol ${entryName}.`);
    return { ok: errors.length === 0, errors, labels, statements, image, dataSymbols, instructionMap, entry: actualEntry, entryAddress, instructionCount: instructionMap.size, sourceLines: lines.length };
  }

  function initMachine(compiled) {
    return { registers: { A: 0, X: 0, L: 0, PC: compiled.entry, SW: 0 }, memory: new Map(compiled.image), cycles: 0, halted: false, status: 'READY', lastLine: -1, lastMessage: 'Machine initialized · waiting for input' };
  }

  function setStatus(status) {
    const pill = document.getElementById('statusPill');
    pill.className = `status-pill ${status.toLowerCase()}`;
    document.getElementById('statusText').textContent = status;
  }

  function compileAndReset() {
    pause();
    const compiled = assemble(editor.value);
    state.compiled = compiled;
    state.dirty = false;
    editor.dataset.dirty = 'false';
    if (!compiled.ok) {
      state.machine = null;
      state.history = [];
      setStatus('ERROR');
      document.getElementById('compileMessage').textContent = `${compiled.errors.length} assembly error${compiled.errors.length === 1 ? '' : 's'}`;
      document.getElementById('compileMessage').style.color = '#c75660';
      document.getElementById('machineNote').textContent = 'Fix the source errors, then run again';
      document.getElementById('outputMain').textContent = 'Assembly needs attention';
      document.getElementById('outputDetail').textContent = compiled.errors[0];
      document.getElementById('outputState').textContent = 'ASSEMBLY ERROR';
      document.getElementById('passValue').textContent = '—';
      document.getElementById('failValue').textContent = '—';
      renderRegisters(); renderMemory(); renderTrace(); updateGutter();
      setNotification(compiled.errors[0]);
      return false;
    }
    state.machine = initMachine(compiled);
    state.history = [];
    state.touched = new Set();
    state.lastRegisterValues = {};
    setStatus('READY');
    document.getElementById('compileMessage').textContent = `${compiled.instructionCount} instructions assembled`;
    document.getElementById('compileMessage').style.color = '';
    document.getElementById('machineNote').textContent = `Entry point · ${hex(compiled.entry)} · ${compiled.instructionCount} instructions`;
    document.getElementById('outputMain').textContent = 'Ready to run';
    document.getElementById('outputDetail').textContent = `Execution begins at ${hex(compiled.entry)}. Use Step to advance one instruction.`;
    document.getElementById('outputState').textContent = 'READY TO RUN';
    document.getElementById('passValue').textContent = '0';
    document.getElementById('failValue').textContent = '0';
    renderRegisters(); renderMemory(); renderTrace(); updateGutter();
    return true;
  }

  function resolveAddress(operand, registers, compiled) {
    const match = String(operand).trim().match(/^(.*?)(?:,\s*X)?$/i);
    const baseText = match ? match[1].replace(/^#/, '').trim() : String(operand).trim();
    const indexed = /,\s*X$/i.test(String(operand).trim());
    const base = numeric(baseText) ?? compiled.labels.get(baseText.toUpperCase());
    if (base === undefined || base === null) throw new Error(`Cannot resolve operand ${operand}.`);
    return base + (indexed ? registers.X : 0);
  }

  function operandValue(operand, registers, compiled, machine) {
    const clean = String(operand).trim();
    if (clean.startsWith('#')) {
      const immediate = numeric(clean.slice(1));
      if (immediate !== null) return immediate;
      const labelAddress = compiled.labels.get(clean.slice(1).toUpperCase());
      if (labelAddress !== undefined) return labelAddress;
    }
    const address = resolveAddress(clean, registers, compiled);
    return machine.memory.get(address) ?? 0;
  }

  function setPC(machine, target, line) {
    machine.registers.PC = target;
    if (line) machine.lastLine = line.line;
  }

  function step() {
    if (state.dirty || !state.compiled) {
      if (!compileAndReset()) return false;
    }
    const { compiled, machine } = state;
    if (!machine || machine.halted) return false;
    const pc = machine.registers.PC;
    const instruction = compiled.instructionMap.get(pc);
    if (!instruction) {
      machine.halted = true;
      machine.status = 'HALTED';
      pause();
      setStatus('HALTED');
      document.getElementById('machineNote').textContent = `No instruction at ${hex(pc)} · machine halted`;
      document.getElementById('outputMain').textContent = 'Program halted';
      document.getElementById('outputDetail').textContent = 'The program counter reached an address with no instruction.';
      renderAll();
      return false;
    }
    const regs = machine.registers;
    const nextPc = pc + 3;
    regs.PC = nextPc;
    let detail = '';
    let writes = [];
    try {
      const op = instruction.op;
      const operand = instruction.operand;
      const value = () => operandValue(operand, regs, compiled, machine);
      const address = () => resolveAddress(operand, regs, compiled);
      switch (op) {
        case 'LDA': regs.A = word(value()); detail = `A ← ${regs.A}`; break;
        case 'LDX': regs.X = word(value()); detail = `X ← ${regs.X}`; break;
        case 'STA': { const at = address(); machine.memory.set(at, word(regs.A)); state.touched.add(at); writes.push(at); detail = `M[${hex(at)}] ← ${regs.A}`; break; }
        case 'STX': { const at = address(); machine.memory.set(at, word(regs.X)); state.touched.add(at); writes.push(at); detail = `M[${hex(at)}] ← ${regs.X}`; break; }
        case 'ADD': regs.A = word(regs.A + value()); detail = `A ← ${regs.A}`; break;
        case 'SUB': regs.A = word(regs.A - value()); detail = `A ← ${regs.A}`; break;
        case 'MUL': regs.A = word(regs.A * value()); detail = `A ← ${regs.A}`; break;
        case 'DIV': { const divisor = value(); if (divisor === 0) throw new Error('Division by zero.'); regs.A = word(Math.trunc(regs.A / divisor)); detail = `A ← ${regs.A}`; break; }
        case 'COMP': { const rhs = value(); regs.SW = regs.A < rhs ? -1 : regs.A > rhs ? 1 : 0; detail = `A ${regs.SW < 0 ? '<' : regs.SW > 0 ? '>' : '='} ${rhs}`; break; }
        case 'TIX': { regs.X = word(regs.X + 1); const rhs = value(); regs.SW = regs.X < rhs ? -1 : regs.X > rhs ? 1 : 0; detail = `X ← ${regs.X} · compare ${rhs}`; break; }
        case 'J': setPC(machine, compiled.labels.get(operand.trim().toUpperCase()) ?? numeric(operand), instruction); detail = `jump → ${hex(regs.PC)}`; break;
        case 'JEQ': case 'JGT': case 'JLT': {
          const take = op === 'JEQ' ? regs.SW === 0 : op === 'JGT' ? regs.SW > 0 : regs.SW < 0;
          if (take) setPC(machine, compiled.labels.get(operand.trim().toUpperCase()) ?? numeric(operand), instruction);
          detail = `${take ? 'branch taken' : 'branch skipped'}${take ? ` → ${hex(regs.PC)}` : ''}`;
          break;
        }
        case 'JSUB': regs.L = nextPc; setPC(machine, compiled.labels.get(operand.trim().toUpperCase()) ?? numeric(operand), instruction); detail = `L ← ${hex(regs.L)} · call`; break;
        case 'RSUB': if (regs.L) regs.PC = regs.L; else machine.halted = true; detail = machine.halted ? 'return · program complete' : `return → ${hex(regs.PC)}`; break;
        default: throw new Error(`Unsupported instruction ${op}.`);
      }
      machine.cycles++;
      machine.lastLine = instruction.line;
      machine.status = machine.halted ? 'HALTED' : 'RUNNING';
      state.history.unshift({ kind: 'step', tick: machine.cycles, address: pc, line: instruction.line, op: instruction.op, operand: instruction.operand, detail, writes });
      state.history = state.history.slice(0, 70);
      if (machine.halted) {
        pause();
        setStatus('HALTED');
        document.getElementById('machineNote').textContent = `Completed in ${machine.cycles} instructions`;
        document.getElementById('outputMain').textContent = 'Program completed successfully';
        document.getElementById('outputState').textContent = 'EXECUTION COMPLETE';
      } else {
        setStatus(state.timer ? 'RUNNING' : 'PAUSED');
        document.getElementById('machineNote').textContent = `Executing line ${instruction.line} · cycle ${machine.cycles}`;
        document.getElementById('outputMain').textContent = `Cycle ${machine.cycles} · ${instruction.op}${instruction.operand ? ` ${instruction.operand}` : ''}`;
        document.getElementById('outputDetail').textContent = detail;
        document.getElementById('outputState').textContent = state.timer ? 'RUNNING' : 'STEPPING';
      }
      if (compiled.labels.has('PASS')) document.getElementById('passValue').textContent = machine.memory.get(compiled.labels.get('PASS')) ?? 0;
      if (compiled.labels.has('FAIL')) document.getElementById('failValue').textContent = machine.memory.get(compiled.labels.get('FAIL')) ?? 0;
      renderAll();
      return !machine.halted;
    } catch (error) {
      machine.halted = true;
      machine.status = 'ERROR';
      pause();
      setStatus('ERROR');
      document.getElementById('machineNote').textContent = `Runtime error · line ${instruction.line}`;
      document.getElementById('outputMain').textContent = 'Execution stopped';
      document.getElementById('outputDetail').textContent = `Line ${instruction.line}: ${error.message}`;
      document.getElementById('outputState').textContent = 'RUNTIME ERROR';
      setNotification(`Line ${instruction.line}: ${error.message}`);
      renderAll();
      return false;
    }
  }

  function pause() {
    if (state.timer) clearInterval(state.timer);
    state.timer = null;
    document.getElementById('runLabel').textContent = 'Run program';
    document.getElementById('runIcon').innerHTML = '<path d="m8 5 11 7-11 7z" fill="currentColor"/>';
  }
  function run() {
    if (state.timer) {
      pause();
      if (state.machine && !state.machine.halted) setStatus('PAUSED');
      document.getElementById('outputState').textContent = 'PAUSED';
      return;
    }
    if (state.dirty || !state.compiled || !state.machine || state.machine.halted) {
      if (!compileAndReset()) return;
    }
    document.getElementById('runLabel').textContent = 'Pause';
    document.getElementById('runIcon').innerHTML = '<path d="M7 5h3v14H7zm7 0h3v14h-3z" fill="currentColor"/>';
    setStatus('RUNNING');
    document.getElementById('outputState').textContent = 'RUNNING';
    const speed = Number(document.getElementById('speedInput').value);
    const delay = Math.round(680 / (0.5 + speed * 0.42));
    state.timer = setInterval(() => { if (!step()) pause(); }, delay);
  }

  function renderRegisters() {
    if (!state.machine) {
      registerGrid.innerHTML = RENDER_REGS.map(([name, label]) => `<div class="register"><div class="register-top">${name}<span class="register-code">${label}</span></div><div class="register-value">—</div></div>`).join('');
      return;
    }
    const regs = state.machine.registers;
    registerGrid.innerHTML = RENDER_REGS.map(([name, label]) => {
      const value = regs[name] ?? 0;
      const display = name === 'PC' ? `${hex(value)} <span style="color:#99a1b0">· ${value}</span>` : `${value} <span style="color:#99a1b0">· ${hex(value)}</span>`;
      const changed = state.lastRegisterValues[name] !== undefined && state.lastRegisterValues[name] !== value;
      state.lastRegisterValues[name] = value;
      return `<div class="register${changed ? ' changed' : ''}"><div class="register-top">${name}<span class="register-code">${label}</span></div><div class="register-value${name === 'PC' ? ' pc-value' : ''}">${display}</div></div>`;
    }).join('');
    if (state.machine.lastLine) updateGutter(state.machine.lastLine);
  }

  function getMemoryEntries() {
    if (!state.compiled || !state.machine) return [];
    const { dataSymbols } = state.compiled;
    const entries = [];
    for (let s = 0; s < dataSymbols.length; s++) {
      const symbol = dataSymbols[s];
      let count = symbol.kind === 'RESW' ? symbol.count : 1;
      if (symbol.kind === 'WORD') {
        const next = dataSymbols[s + 1];
        if (next && next.address > symbol.address) count = Math.max(1, Math.min(32, Math.floor((next.address - symbol.address) / 3)));
        else count = 1;
      }
      count = Math.min(count, 32);
      for (let i = 0; i < count; i++) {
        const address = symbol.address + i * 3;
        const indexed = count > 1;
        entries.push({ name: indexed ? `${symbol.name}[${i}]` : symbol.name, address, value: state.machine.memory.get(address) ?? 0 });
      }
    }
    return entries;
  }

  function renderMemory() {
    const entries = getMemoryEntries();
    document.getElementById('memoryCount').textContent = `${entries.length} word${entries.length === 1 ? '' : 's'}`;
    const filter = memorySearch.value.trim().toUpperCase();
    const visible = entries.filter(entry => !filter || entry.name.toUpperCase().includes(filter) || hex(entry.address).includes(filter));
    if (!visible.length) {
      memoryRows.innerHTML = `<tr><td class="memory-empty" colspan="3">${entries.length ? 'No matching memory words' : 'Assemble source to inspect memory'}</td></tr>`;
      return;
    }
    memoryRows.innerHTML = visible.map(entry => `<tr><td class="symbol">${escapeHtml(entry.name)}</td><td class="address">${hex(entry.address)}</td><td class="value${state.touched.has(entry.address) ? ' touched' : ''}">${entry.value} <span style="color:#a2aaba">· ${hex(entry.value)}</span></td></tr>`).join('');
  }

  function renderTrace() {
    const steps = state.history.filter(item => item.kind === 'step').length;
    document.getElementById('traceCount').textContent = `${steps} step${steps === 1 ? '' : 's'}`;
    if (!state.history.length) {
      traceList.innerHTML = '<div class="trace-empty">Press <strong>Run program</strong> or <strong>Step</strong> to begin execution.</div>';
      return;
    }
    const rows = state.history.slice(0, 9).map(item => {
      if (item.kind === 'log') return `<div class="trace-row"><span class="trace-tick">${escapeHtml(item.time)}</span><span class="trace-addr">SYSTEM</span><span class="trace-op">${escapeHtml(item.message)}</span><span class="trace-result">${escapeHtml(item.tone)}</span><span class="trace-cycle"></span></div>`;
      return `<div class="trace-row"><span class="trace-tick">#${item.tick}</span><span class="trace-addr">${hex(item.address)}</span><span class="trace-op">${escapeHtml(item.op)}${item.operand ? ` ${escapeHtml(item.operand)}` : ''}</span><span class="trace-result">${escapeHtml(item.detail)}</span><span class="trace-cycle">line ${item.line}</span></div>`;
    }).join('');
    traceList.innerHTML = rows;
  }

  function renderAll() { renderRegisters(); renderMemory(); renderTrace(); }
  function updateGutter(activeLine = state.machine?.lastLine || 0) {
    const count = editor.value.split('\n').length;
    gutter.innerHTML = Array.from({ length: count }, (_, i) => `<div class="line-no${i + 1 === activeLine ? ' active' : ''}">${i + 1}</div>`).join('');
    document.getElementById('lineCount').textContent = `${count} line${count === 1 ? '' : 's'}`;
    gutter.scrollTop = editor.scrollTop;
  }

  editor.value = sample;
  editor.addEventListener('input', () => {
    state.dirty = true;
    document.getElementById('compileMessage').textContent = 'Source changed · assemble to update';
    document.getElementById('compileMessage').style.color = '#b77820';
    updateGutter();
  });
  editor.addEventListener('scroll', () => { gutter.scrollTop = editor.scrollTop; });
  editor.addEventListener('keydown', event => {
    if (event.key === 'Tab') {
      event.preventDefault();
      const start = editor.selectionStart, end = editor.selectionEnd;
      editor.setRangeText('    ', start, end, 'end');
      editor.dispatchEvent(new Event('input'));
    }
    if ((event.ctrlKey || event.metaKey) && event.key === 'Enter') { event.preventDefault(); run(); }
  });
  runButton.addEventListener('click', run);
  document.getElementById('stepButton').addEventListener('click', () => { if (state.timer) pause(); step(); });
  document.getElementById('resetButton').addEventListener('click', compileAndReset);
  document.getElementById('sampleButton').addEventListener('click', () => { pause(); editor.value = sample; state.dirty = true; updateGutter(); compileAndReset(); });
  document.getElementById('downloadButton').addEventListener('click', () => {
    const blob = new Blob([editor.value], { type: 'text/plain;charset=utf-8' });
    const url = URL.createObjectURL(blob);
    const anchor = document.createElement('a');
    anchor.href = url; anchor.download = 'EX1.asm'; anchor.click();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  });
  memorySearch.addEventListener('input', renderMemory);
  document.getElementById('speedInput').addEventListener('input', event => {
    const value = Number(event.target.value);
    document.getElementById('speedValue').textContent = `${(value / 4).toFixed(1)}×`;
    if (state.timer) { pause(); run(); }
  });
  document.addEventListener('keydown', event => {
    if (event.key === 'F10') { event.preventDefault(); if (state.timer) pause(); step(); }
  });

  updateGutter();
  compileAndReset();
})();
