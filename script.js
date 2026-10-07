/* =====================================================
   CFG Simplifier — Universal Input Edition
   =====================================================

   Pipeline:
     1. Parse
     2. Remove Null (ε) productions
     3. Remove Unit productions
     4. Remove Useless Symbols (non-generating, then unreachable)

   Accepts any valid CFG input:
     - ε, eps, epsilon, e, @, λ, lambda → treated as empty
     - | for alternatives
     - ->, ::=, → all accepted as arrow
     - Multi-character nonterminals (Expr, Stmt, Term)
     - Single-line or multi-line
     - Comments after #
     - Spaces or no spaces between symbols
   ===================================================== */

const EPSILON_TOKENS = new Set(["ε", "eps", "epsilon", "e", "@", "λ", "lambda"]);

/* =====================================================
   TAB SWITCHING
   ===================================================== */
document.querySelectorAll(".tab").forEach(tab => {
  tab.addEventListener("click", () => {
    document.querySelectorAll(".tab").forEach(t => t.classList.remove("active"));
    document.querySelectorAll(".view").forEach(v => v.classList.remove("active"));
    tab.classList.add("active");
    document.getElementById("view-" + tab.dataset.view).classList.add("active");
  });
});

/* =====================================================
   EXAMPLE GRAMMARS
   ===================================================== */
const EXAMPLES = {
  null: `S -> A B | ε
A -> a | ε
B -> b | ε`,
  unit: `S -> A | B
A -> a
B -> b`,
  useless: `S -> abS | abA | abB
A -> cd
B -> aB
C -> dc`,
  both: `S -> A B | ε
A -> B
B -> b | ε`
};

document.querySelectorAll(".chip[data-example]").forEach(chip => {
  chip.addEventListener("click", () => {
    document.getElementById("grammarInput").value = EXAMPLES[chip.dataset.example];
    resetOutputs();
  });
});

/* =====================================================
   TOKENIZER — handles multi-char nonterminals
   ===================================================== */
function tokenizeRHS(rhsRaw, knownLHS) {
  const cleaned = rhsRaw.trim();
  if (!cleaned) return [];

  // If user separated symbols by spaces, honor that
  if (/\s/.test(cleaned)) {
    return cleaned.split(/\s+/).filter(Boolean);
  }

  // No spaces: greedily match known LHS names first
  const tokens = [];
  let i = 0;
  while (i < cleaned.length) {
    let matched = false;
    for (let len = Math.min(6, cleaned.length - i); len >= 1; len--) {
      const chunk = cleaned.substr(i, len);
      if (knownLHS.has(chunk)) {
        tokens.push(chunk);
        i += len;
        matched = true;
        break;
      }
    }
    if (!matched) {
      tokens.push(cleaned[i]);
      i++;
    }
  }
  return tokens;
}

/* =====================================================
   PARSING
   ===================================================== */
function parseGrammar(text) {
  const grammar = {};
  const errors = [];
  const lines = text
    .split("\n")
    .map(l => l.replace(/#.*$/, "").trim())
    .filter(Boolean);

  if (lines.length === 0) {
    return { grammar, errors: ["Input is empty."] };
  }

  // Pass 1: collect LHS names
  const lhsNames = new Set();
  for (const line of lines) {
    const idx = line.search(/(-?>|::=|→)/);
    if (idx <= 0) continue;
    const lhs = line.slice(0, idx).trim();
    if (lhs) lhsNames.add(lhs);
  }

  // Pass 2: parse productions
  for (const line of lines) {
    const arrowMatch = line.match(/(-?>|::=|→)/);
    if (!arrowMatch) {
      errors.push(`No arrow found: "${line}"`);
      continue;
    }
    const arrowIdx = line.search(/(-?>|::=|→)/);
    const arrowLen = arrowMatch[0].length;
    const lhs = line.slice(0, arrowIdx).trim();
    const rhsRaw = line.slice(arrowIdx + arrowLen).trim();

    if (!lhs) {
      errors.push(`Missing LHS in: "${line}"`);
      continue;
    }

    const alts = rhsRaw.split("|").map(s => s.trim());

    if (!grammar[lhs]) grammar[lhs] = [];
    for (const alt of alts) {
      if (alt === "" || EPSILON_TOKENS.has(alt.toLowerCase())) {
        if (!grammar[lhs].includes("ε")) grammar[lhs].push("ε");
      } else {
        const tokens = tokenizeRHS(alt, lhsNames);
        const normalized = tokens.join(" ");
        if (!grammar[lhs].includes(normalized)) {
          grammar[lhs].push(normalized);
        }
      }
    }
  }

  for (const lhs of lhsNames) {
    if (!grammar[lhs]) grammar[lhs] = ["ε"];
  }

  return { grammar, errors };
}

/* =====================================================
   HELPERS
   ===================================================== */
function countProductions(g) {
  return Object.values(g).reduce((n, r) => n + r.length, 0);
}

function isNonTerminal(sym, grammar) {
  return Object.prototype.hasOwnProperty.call(grammar, sym);
}

function isUnitProduction(rhs, grammar) {
  const parts = rhs.split(/\s+/).filter(Boolean);
  return parts.length === 1 && isNonTerminal(parts[0], grammar);
}

function isEpsilonRHS(rhs) {
  if (rhs === "ε") return true;
  const parts = rhs.split(/\s+/).filter(Boolean);
  return parts.length === 0 ||
         (parts.length === 1 && EPSILON_TOKENS.has(parts[0].toLowerCase()));
}

/* =====================================================
   STEP 1 — NULLABLE VARIABLES
   ===================================================== */
function findNullable(grammar, steps) {
  const nullable = new Set();
  let changed = true;

  while (changed) {
    changed = false;
    for (const [lhs, rhsList] of Object.entries(grammar)) {
      for (const rhs of rhsList) {
        const parts = rhs.split(/\s+/).filter(Boolean);

        if (isEpsilonRHS(rhs)) {
          if (!nullable.has(lhs)) {
            nullable.add(lhs);
            steps.push({
              phase: "Null",
              desc: `<code>${lhs}</code> is nullable (has ε-production)`
            });
            changed = true;
          }
        } else if (parts.length > 0 && parts.every(p => nullable.has(p))) {
          if (!nullable.has(lhs)) {
            nullable.add(lhs);
            steps.push({
              phase: "Null",
              desc: `<code>${lhs}</code> is nullable (all symbols in <code>${rhs}</code> are nullable)`
            });
            changed = true;
          }
        }
      }
    }
  }
  return nullable;
}

/* =====================================================
   STEP 2 — REMOVE NULL PRODUCTIONS
   Keeps S → ε if S is start symbol and nullable.
   ===================================================== */
function removeNullProductions(grammar, steps) {
  const nullable = findNullable(grammar, steps);
  const newGrammar = {};
  const startSymbol = Object.keys(grammar)[0];

  for (const [lhs, rhsList] of Object.entries(grammar)) {
    const newRHS = new Set();

    for (const rhs of rhsList) {
      const parts = rhs.split(/\s+/).filter(Boolean);

      if (isEpsilonRHS(rhs)) {
        if (lhs === startSymbol) {
          newRHS.add("ε");
          steps.push({
            phase: "Null",
            desc: `Kept <code>${lhs} → ε</code> (start symbol, preserves ε ∈ L(G))`
          });
        } else {
          steps.push({
            phase: "Null",
            desc: `Dropped <code>${lhs} → ε</code>`
          });
        }
        continue;
      }

      const n = parts.length;
      for (let mask = 0; mask < (1 << n); mask++) {
        const combo = parts.filter((sym, i) =>
          !(nullable.has(sym) && (mask & (1 << i)))
        );
        if (combo.length > 0) newRHS.add(combo.join(" "));
      }
    }

    if (newRHS.size > 0) newGrammar[lhs] = [...newRHS];
  }

  steps.push({
    phase: "Null",
    desc: `Nullable set = { ${[...nullable].join(", ") || "∅"} }. All ε-productions processed.`
  });

  return { grammar: newGrammar, nullable };
}

/* =====================================================
   STEP 3 — UNIT PAIRS
   ===================================================== */
function findUnitPairs(grammar) {
  const units = {};
  for (const lhs of Object.keys(grammar)) units[lhs] = new Set([lhs]);

  let changed = true;
  while (changed) {
    changed = false;
    for (const [lhs, rhsList] of Object.entries(grammar)) {
      for (const rhs of rhsList) {
        const parts = rhs.split(/\s+/).filter(Boolean);
        if (parts.length === 1 && isNonTerminal(parts[0], grammar)) {
          const target = parts[0];
          for (const u of units[target]) {
            if (!units[lhs].has(u)) {
              units[lhs].add(u);
              changed = true;
            }
          }
        }
      }
    }
  }
  return units;
}

/* =====================================================
   STEP 4 — REMOVE UNIT PRODUCTIONS
   ===================================================== */
function removeUnitProductions(grammar, steps) {
  const unitPairs = findUnitPairs(grammar);
  const newGrammar = {};

  for (const [lhs, reachable] of Object.entries(unitPairs)) {
    const newRHS = new Set();
    for (const B of reachable) {
      for (const rhs of (grammar[B] || [])) {
        if (!isUnitProduction(rhs, grammar)) newRHS.add(rhs);
      }
    }
    if (newRHS.size > 0) newGrammar[lhs] = [...newRHS];
  }

  const totalPairs = Object.values(unitPairs)
    .reduce((n, s) => n + Math.max(0, s.size - 1), 0);

  steps.push({
    phase: "Unit",
    desc: `Removed all unit productions. ${totalPairs} unit pair(s) collapsed.`
  });

  return { grammar: newGrammar, unitPairs };
}

/* =====================================================
   STEP 5 — FIND GENERATING VARIABLES
   A variable is generating if it can derive a terminal string
   ===================================================== */
function findGenerating(grammar) {
  const generating = new Set();
  let changed = true;

  while (changed) {
    changed = false;
    for (const [lhs, rhsList] of Object.entries(grammar)) {
      if (generating.has(lhs)) continue;
      for (const rhs of rhsList) {
        if (isEpsilonRHS(rhs)) {
          generating.add(lhs);
          changed = true;
          break;
        }
        const parts = rhs.split(/\s+/).filter(Boolean);
        const allGenerating = parts.every(p =>
          !isNonTerminal(p, grammar) || generating.has(p)
        );
        if (parts.length > 0 && allGenerating) {
          generating.add(lhs);
          changed = true;
          break;
        }
      }
    }
  }
  return generating;
}

/* =====================================================
   STEP 6 — FIND REACHABLE VARIABLES FROM START
   ===================================================== */
function findReachable(grammar, startSymbol) {
  const reachable = new Set([startSymbol]);
  let changed = true;
  while (changed) {
    changed = false;
    for (const A of [...reachable]) {
      const rhsList = grammar[A] || [];
      for (const rhs of rhsList) {
        const parts = rhs.split(/\s+/).filter(Boolean);
        for (const p of parts) {
          if (isNonTerminal(p, grammar) && !reachable.has(p)) {
            reachable.add(p);
            changed = true;
          }
        }
      }
    }
  }
  return reachable;
}

/* =====================================================
   STEP 7 — REMOVE USELESS SYMBOLS
   (non-generating first, then unreachable)
   ===================================================== */
function removeUselessSymbols(grammar, steps) {
  const startSymbol = Object.keys(grammar)[0];

  /* --- 7a. Remove non-generating --- */
  const generating = findGenerating(grammar);
  const nonGenerating = Object.keys(grammar).filter(v => !generating.has(v));

  let g1 = {};
  for (const [lhs, rhsList] of Object.entries(grammar)) {
    if (!generating.has(lhs)) continue;
    const newRHS = rhsList.filter(rhs => {
      if (isEpsilonRHS(rhs)) return true;
      const parts = rhs.split(/\s+/).filter(Boolean);
      return parts.every(p =>
        !isNonTerminal(p, grammar) || generating.has(p)
      );
    });
    if (newRHS.length > 0) g1[lhs] = newRHS;
  }

  if (nonGenerating.length > 0) {
    steps.push({
      phase: "Useless",
      desc: `Non-generating removed: <code>{ ${nonGenerating.join(", ")} }</code> (cannot derive any terminal string)`
    });
  }

  /* --- 7b. Remove unreachable from g1 --- */
  const reachable = findReachable(g1, startSymbol);
  const unreachable = Object.keys(g1).filter(v => !reachable.has(v));

  const finalGrammar = {};
  for (const [lhs, rhsList] of Object.entries(g1)) {
    if (!reachable.has(lhs)) continue;
    finalGrammar[lhs] = rhsList;
  }

  if (unreachable.length > 0) {
    steps.push({
      phase: "Useless",
      desc: `Unreachable removed: <code>{ ${unreachable.join(", ")} }</code> (no path from start symbol)`
    });
  }

  if (nonGenerating.length === 0 && unreachable.length === 0) {
    steps.push({
      phase: "Useless",
      desc: `No useless symbols found — all variables are generating and reachable.`
    });
  }

  return {
    grammar: finalGrammar,
    nonGenerating,
    unreachable,
    generating,
    reachable
  };
}

/* =====================================================
   RENDERING
   ===================================================== */
function renderGrammar(grammar, containerId) {
  const el = document.getElementById(containerId);
  if (!grammar || Object.keys(grammar).length === 0) {
    el.innerHTML = `<em class="placeholder">∅ (empty grammar)</em>`;
    return;
  }
  el.innerHTML = Object.entries(grammar)
    .map(([lhs, rhs]) => `<div class="prod"><b>${lhs}</b> → ${rhs.join(" | ")}</div>`)
    .join("");
}

function renderLog(steps) {
  const el = document.getElementById("log");
  if (!steps.length) {
    el.innerHTML = `<div class="log-empty">No steps yet.</div>`;
    return;
  }
  el.innerHTML = steps.map((s, i) => {
    let cls = "";
    if (s.phase === "Unit") cls = "unit";
    else if (s.phase === "Useless") cls = "useless";
    return `
      <div class="log-item" style="animation-delay:${i * 0.04}s">
        <span class="phase ${cls}">${s.phase}</span>
        <div class="desc">${s.desc}</div>
      </div>
    `;
  }).join("");
  el.scrollTop = el.scrollHeight;
}

function renderPills(containerId, items, cls = "") {
  const el = document.getElementById(containerId);
  if (!el) return;
  if (!items || items.length === 0) {
    el.innerHTML = `<span class="muted">—</span>`;
    return;
  }
  el.innerHTML = items.map((x, i) =>
    `<span class="pill ${cls}" style="animation-delay:${i * 0.04}s">${x}</span>`
  ).join("");
}

function setStageState(id, state) {
  const el = document.getElementById(id);
  if (!el) return;
  el.classList.remove("active", "done");
  if (state) el.classList.add(state);
}

function animateNumber(el, target) {
  if (!el) return;
  const start = parseInt(el.textContent, 10) || 0;
  const duration = 500;
  const t0 = performance.now();

  function tick(now) {
    const t = Math.min(1, (now - t0) / duration);
    const eased = 1 - Math.pow(1 - t, 3);
    const val = Math.round(start + (target - start) * eased);
    el.textContent = val;
    if (t < 1) requestAnimationFrame(tick);
  }
  requestAnimationFrame(tick);
}

/* =====================================================
   MAIN PIPELINE
   ===================================================== */
function run() {
  const input = document.getElementById("grammarInput").value;
  const steps = [];

  /* Stage 1 — Parse */
  setStageState("stage-parse", "active");
  const { grammar: original, errors } = parseGrammar(input);
  setStageState("stage-parse", "done");

  if (errors.length > 0) {
    document.getElementById("out-parse").innerHTML =
      `<span style="color:var(--danger)">⚠ ${errors.join("<br>⚠ ")}</span>`;
    ["out-null", "out-unit", "out-useless", "out-final"].forEach(id => {
      const el = document.getElementById(id);
      if (el) el.innerHTML = `<em class="placeholder">—</em>`;
    });
    document.getElementById("log").innerHTML =
      `<div class="log-empty" style="color:var(--danger)">Fix input errors and try again.</div>`;
    renderPills("nullableBox", []);
    renderPills("unitBox", []);
    renderPills("uselessBox", []);
    animateNumber(document.getElementById("stat-prod"), 0);
    animateNumber(document.getElementById("stat-null"), 0);
    animateNumber(document.getElementById("stat-unit"), 0);
    animateNumber(document.getElementById("stat-removed"), 0);
    return;
  }

  if (Object.keys(original).length === 0) {
    document.getElementById("out-parse").innerHTML =
      `<span style="color:var(--danger)">No productions found. Check your syntax.</span>`;
    return;
  }

  renderGrammar(original, "out-parse");
  const originalCount = countProductions(original);

  /* Stage 2 — Null removal */
  setStageState("stage-null", "active");
  const { grammar: afterNull, nullable } = removeNullProductions(original, steps);
  renderGrammar(afterNull, "out-null");
  setStageState("stage-null", "done");

  /* Stage 3 — Unit removal */
  setStageState("stage-unit", "active");
  const { grammar: afterUnit, unitPairs } = removeUnitProductions(afterNull, steps);
  renderGrammar(afterUnit, "out-unit");
  setStageState("stage-unit", "done");

  /* Stage 4 — Useless removal */
  setStageState("stage-useless", "active");
  const {
    grammar: finalGrammar,
    nonGenerating,
    unreachable
  } = removeUselessSymbols(afterUnit, steps);
  renderGrammar(finalGrammar, "out-useless");
  setStageState("stage-useless", "done");

  /* Stage 5 — Final */
  setStageState("stage-final", "active");
  renderGrammar(finalGrammar, "out-final");
  setStageState("stage-final", "done");

  /* Log + Pills */
  renderLog(steps);

  renderPills("nullableBox", [...nullable]);
  renderPills(
    "unitBox",
    Object.entries(unitPairs).map(([a, b]) => `${a}→{${[...b].join(",")}}`),
    "amber"
  );
  const uselessItems = [
    ...nonGenerating.map(v => `${v} (non-generating)`),
    ...unreachable.map(v => `${v} (unreachable)`)
  ];
  renderPills("uselessBox", uselessItems, "amber");

  /* Stats */
  const finalCount = countProductions(finalGrammar);
  animateNumber(document.getElementById("stat-prod"), finalCount);
  animateNumber(document.getElementById("stat-null"), nullable.size);
  animateNumber(document.getElementById("stat-unit"), Object.keys(unitPairs).length);
  animateNumber(document.getElementById("stat-removed"),
    Math.max(0, originalCount - finalCount));

  launchConfetti();
}

/* =====================================================
   RESET
   ===================================================== */
function resetOutputs() {
  ["out-parse", "out-null", "out-unit", "out-useless", "out-final"].forEach(id => {
    const el = document.getElementById(id);
    if (el) el.innerHTML = `<em class="placeholder">Waiting…</em>`;
  });
  document.getElementById("log").innerHTML =
    `<div class="log-empty">No steps yet. Hit <b>Run Simplification</b>.</div>`;
  renderPills("nullableBox", []);
  renderPills("unitBox", []);
  renderPills("uselessBox", []);
  ["stat-prod", "stat-null", "stat-unit", "stat-removed"].forEach(id => {
    const el = document.getElementById(id);
    if (el) el.textContent = "0";
  });
  ["stage-parse", "stage-null", "stage-unit", "stage-useless", "stage-final"].forEach(id => {
    setStageState(id, "");
  });
}

/* =====================================================
   COPY / DOWNLOAD
   ===================================================== */
function copyFinal() {
  const el = document.getElementById("out-final");
  const text = el.innerText.trim();
  if (!text || text.includes("Waiting")) {
    alert("Run simplification first.");
    return;
  }
  navigator.clipboard.writeText(text).then(() => {
    const btn = document.getElementById("btn-copy");
    const old = btn.textContent;
    btn.textContent = "Copied ✓";
    setTimeout(() => (btn.textContent = old), 1200);
  }).catch(() => alert("Copy failed."));
}

function downloadFinal() {
  const el = document.getElementById("out-final");
  const text = el.innerText.trim();
  if (!text || text.includes("Waiting")) {
    alert("Run simplification first.");
    return;
  }
  const blob = new Blob([text], { type: "text/plain" });
  const a = document.createElement("a");
  a.href = URL.createObjectURL(blob);
  a.download = "simplified-grammar.txt";
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  URL.revokeObjectURL(a.href);
}

/* =====================================================
   CONFETTI
   ===================================================== */
function launchConfetti() {
  const canvas = document.getElementById("confetti");
  if (!canvas) return;
  const ctx = canvas.getContext("2d");
  canvas.width = window.innerWidth;
  canvas.height = window.innerHeight;

  const colors = ["#14b8a6", "#f59e0b", "#fbbf24", "#2dd4bf", "#4ade80"];
  const pieces = [];
  for (let i = 0; i < 70; i++) {
    pieces.push({
      x: canvas.width * 0.5 + (Math.random() - 0.5) * 300,
      y: canvas.height * 0.3,
      vx: (Math.random() - 0.5) * 8,
      vy: Math.random() * -8 - 3,
      size: Math.random() * 6 + 3,
      color: colors[Math.floor(Math.random() * colors.length)],
      rot: Math.random() * Math.PI * 2,
      vr: (Math.random() - 0.5) * 0.3,
      life: 1
    });
  }

  function tick() {
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    let alive = false;
    for (const p of pieces) {
      if (p.life <= 0) continue;
      alive = true;
      p.x += p.vx;
      p.y += p.vy;
      p.vy += 0.35;
      p.vx *= 0.99;
      p.rot += p.vr;
      p.life -= 0.012;

      ctx.save();
      ctx.globalAlpha = Math.max(0, p.life);
      ctx.translate(p.x, p.y);
      ctx.rotate(p.rot);
      ctx.fillStyle = p.color;
      ctx.fillRect(-p.size / 2, -p.size / 2, p.size, p.size);
      ctx.restore();
    }
    if (alive) requestAnimationFrame(tick);
    else ctx.clearRect(0, 0, canvas.width, canvas.height);
  }
  tick();
}

/* =====================================================
   CURSOR GLOW
   ===================================================== */
const cursorGlow = document.getElementById("cursorGlow");
if (cursorGlow) {
  let mx = 0, my = 0, gx = 0, gy = 0;
  document.addEventListener("mousemove", e => {
    mx = e.clientX; my = e.clientY;
    cursorGlow.style.opacity = "1";
  });
  document.addEventListener("mouseleave", () => {
    cursorGlow.style.opacity = "0";
  });
  (function loop() {
    gx += (mx - gx) * 0.12;
    gy += (my - gy) * 0.12;
    cursorGlow.style.left = gx + "px";
    cursorGlow.style.top = gy + "px";
    requestAnimationFrame(loop);
  })();
}

/* =====================================================
   RIPPLE
   ===================================================== */
document.querySelectorAll(".ripple").forEach(btn => {
  btn.addEventListener("mousedown", e => {
    const r = btn.getBoundingClientRect();
    btn.style.setProperty("--mx", (e.clientX - r.left) + "px");
    btn.style.setProperty("--my", (e.clientY - r.top) + "px");
  });
});

/* =====================================================
   EVENT WIRING
   ===================================================== */
document.getElementById("btn-run").addEventListener("click", run);
document.getElementById("btn-reset").addEventListener("click", resetOutputs);
document.getElementById("btn-copy").addEventListener("click", copyFinal);
document.getElementById("btn-download").addEventListener("click", downloadFinal);

/* Ctrl+Enter inside textarea = run */
document.getElementById("grammarInput").addEventListener("keydown", e => {
  if (e.key === "Enter" && (e.ctrlKey || e.metaKey)) {
    e.preventDefault();
    run();
  }
});

/* Auto-run on load */
window.addEventListener("DOMContentLoaded", run);

/* Resize handler for confetti canvas */
window.addEventListener("resize", () => {
  const canvas = document.getElementById("confetti");
  if (canvas) {
    canvas.width = window.innerWidth;
    canvas.height = window.innerHeight;
  }
});