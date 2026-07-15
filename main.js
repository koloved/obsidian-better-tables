"use strict";

const { Plugin, Notice, setIcon, Menu, PluginSettingTab, Setting, MarkdownRenderer, Component, MarkdownRenderChild } = require("obsidian");

const DEFAULT_SETTINGS = {
  // false: click selects a cell, a second click (or Enter) edits it.
  // true:  a single click edits the cell immediately ("quick text edit").
  quickEdit: false
};

const TABLE_CELL_W = 140;
const TABLE_CELL_H = 48;
const MIN_W = 50;
const MIN_H = 28;
const MAX_LINK_SUGGESTIONS = 20;

const SIZE_RE = /^\s*<!--\s*tk:cols=([\d.,\s]*);rows=([\d.,\s]*)(?:;fit=(\d))?\s*-->\s*$/;

function sumArr(a) {
  return a.reduce((s, n) => s + n, 0);
}

/** Split a markdown table row on cell separators, while leaving escaped pipes,
 *  wikilink aliases like [[Page|Alias]], inline code, and markdown link text
 *  intact. The serializer still escapes pipes, but this keeps hand-written
 *  table blocks from falling apart. */
function splitTableRow(inner) {
  const cells = [];
  let cur = "";
  let inCode = false;
  let mathFence = null;
  let wikiDepth = 0;
  let bracketDepth = 0;
  for (let i = 0; i < inner.length; i++) {
    const ch = inner[i];
    const prev = inner[i - 1];
    const next = inner[i + 1];

    if (ch === "`" && prev !== "\\" && !mathFence) inCode = !inCode;
    if (!inCode) {
      if (ch === "$" && prev !== "\\") {
        const fence = next === "$" ? "$$" : "$";
        if (!mathFence) {
          mathFence = fence;
          cur += fence;
          if (fence === "$$") i++;
          continue;
        }
        if (mathFence === fence) {
          mathFence = null;
          cur += fence;
          if (fence === "$$") i++;
          continue;
        }
      }
      if (mathFence) {
        cur += ch;
        continue;
      }
      if (ch === "[" && next === "[") {
        wikiDepth++;
        cur += ch + next;
        i++;
        continue;
      }
      if (ch === "]" && next === "]" && wikiDepth > 0) {
        wikiDepth--;
        cur += ch + next;
        i++;
        continue;
      }
      if (ch === "[" && prev !== "\\" && wikiDepth === 0) bracketDepth++;
      else if (ch === "]" && prev !== "\\" && bracketDepth > 0) bracketDepth--;
    }

    if (ch === "|" && prev !== "\\" && !inCode && wikiDepth === 0 && bracketDepth === 0) {
      cells.push(cur);
      cur = "";
      continue;
    }
    cur += ch;
  }
  cells.push(cur);
  return cells;
}

/** Parse a GitHub-style markdown table into a 2-D array of cell strings.
 *  Ignores the |---| separator line and any non-pipe lines (e.g. our size comment). */
function parseMdTable(text) {
  const lines = text.split("\n").filter((l) => l.trim().startsWith("|"));
  const rows = [];
  for (const line of lines) {
    if (/^\s*\|[\s:|-]+\|\s*$/.test(line) && line.includes("-")) continue;
    const inner = line.trim().replace(/^\|/, "").replace(/\|$/, "");
    rows.push(
      splitTableRow(inner)
        // Decode escaped pipes and our <br> line-break encoding back into the
        // raw multi-line text the cell edits as.
        .map((c) => c.trim().replace(/\\\|/g, "|").replace(/<br\s*\/?>/gi, "\n"))
    );
  }
  if (!rows.length) return null;
  const width = Math.max(...rows.map((r) => r.length));
  for (const r of rows) while (r.length < width) r.push("");
  return rows;
}

function mdFromCells(cells, align) {
  // Pipe tables can't contain a literal pipe or newline, so escape pipes and
  // encode in-cell line breaks (Cmd+Enter) as <br>, which is valid table markup.
  const esc = (s) => s.replace(/\|/g, "\\|").replace(/\n/g, "<br>");
  const row = (r) => "| " + r.map((c) => esc(c) || "   ").join(" | ") + " |";
  // Column alignment lives in the separator row (portable markdown):
  // :---: center, ---: right, --- default/left.
  const sep = cells[0].map((_, c) => {
    const a = align && align[c];
    if (a === "center") return " :---: ";
    if (a === "right") return " ---: ";
    return " --- ";
  });
  return [row(cells[0]), "|" + sep.join("|") + "|", ...cells.slice(1).map(row)].join("\n");
}

/** Read per-column alignment from the table's separator row, if present. */
function parseAlign(text) {
  for (const line of text.split("\n")) {
    if (/^\s*\|[\s:|-]+\|\s*$/.test(line) && line.includes("-")) {
      return line
        .trim()
        .replace(/^\|/, "")
        .replace(/\|$/, "")
        .split("|")
        .map((c) => {
          const s = c.trim();
          const l = s.startsWith(":");
          const r = s.endsWith(":");
          if (l && r) return "center";
          if (r) return "right";
          return null;
        });
    }
  }
  return null;
}

/** Pull stored column/row sizes out of the trailing size comment, if present. */
function parseSizes(text) {
  for (const line of text.split("\n")) {
    const m = line.match(SIZE_RE);
    if (m) {
      const nums = (s) =>
        s.split(",").map((n) => Number(n.trim())).filter((n) => Number.isFinite(n) && n > 0);
      return { cols: nums(m[1]), rows: nums(m[2]), fit: m[3] === "1" };
    }
  }
  return null;
}

class TableWidget {
  constructor(plugin, source, el, ctx) {
    this.plugin = plugin;
    this.source = source;
    this.el = el;
    this.ctx = ctx;
    this.cells = [["", ""], ["", ""]];
    this.colW = [];
    this.rowH = [];
    this.colAlign = [];
    this.editingCell = null;
    this.editingPos = null;
    this.dirty = false;
    this.rootEl = null;
    this.tableEl = null;
    this.addColEl = null;
    this.addRowEl = null;
    this.colHandles = [];
    this.rowHandles = [];
    this.colDividers = [];
    this.rowDividers = [];
    this.insertColDots = [];
    this.insertRowDots = [];
    this.insertLineEl = null;
    this.resizeObs = null;
    this.selected = null;
    this.deleteTableEl = null;
    this.lineSelKey = null;
    this.cellSel = null;
    this.cellSelOutside = null;
    this.cellSelKey = null;
    this.cellSelBox = null;
    // Owns the child components spawned by markdown cell rendering (embeds,
    // dataview, etc.) so they unload when the widget re-renders or tears down,
    // instead of leaking onto the plugin for its whole lifetime.
    this.mdComponent = null;
    // When true the table stretches to fill the page content width instead of
    // being sized by its column pixels. Toggled by the button in the top-right.
    this.pageWidth = false;
  }

  get doc() {
    return this.el.ownerDocument;
  }

  /** Tear down everything this widget owns. Called when Obsidian unloads the
   *  block (re-render, view close, plugin unload) via the render child below. */
  destroy() {
    if (this.resizeObs) {
      this.resizeObs.disconnect();
      this.resizeObs = null;
    }
    this.closeInternalLinkSuggest();
    if (this.mdComponent) {
      this.mdComponent.unload();
      this.mdComponent = null;
    }
  }

  isEditing() {
    return this.editingCell !== null;
  }

  /** Reading view is display-only: no live editor sits behind the block, so the
   *  table renders static (no chrome, no click-to-edit). Obsidian has changed
   *  the exact Live Preview wrapper classes over time, so prefer known
   *  CodeMirror/editing ancestors before falling back to preview/export. */
  isReadingView() {
    const editRoot = this.el.closest(
      ".markdown-source-view, .cm-editor, .cm-content, .cm-contentContainer, .cm-scroller, .cm-preview-code-block, .cm-embed-block"
    );
    if (editRoot) return false;
    const previewRoot = this.el.closest(".markdown-reading-view, .markdown-preview-view");
    if (previewRoot) return true;
    return true;
  }

  loadSizes() {
    const cols = this.cells[0].length;
    const rows = this.cells.length;
    const stored = parseSizes(this.source);
    const pc = stored && stored.cols;
    const pr = stored && stored.rows;
    this.colW = Array.isArray(pc) && pc.length === cols ? pc.map((n) => Math.max(MIN_W, n)) : [];
    this.rowH = Array.isArray(pr) && pr.length === rows ? pr.map((n) => Math.max(MIN_H, n)) : [];
    if (this.colW.length !== cols) this.colW = Array(cols).fill(TABLE_CELL_W);
    if (this.rowH.length !== rows) this.rowH = Array(rows).fill(TABLE_CELL_H);
    // Restore page-width mode from the stored size comment so it survives
    // re-renders triggered by column/row resizes or other saves.
    this.pageWidth = !!(stored && stored.fit);
  }

  loadAlign() {
    const cols = this.cells[0].length;
    const a = parseAlign(this.source);
    this.colAlign = Array.isArray(a) && a.length === cols ? a : Array(cols).fill(null);
  }

  /** Apply per-column text alignment to the cells. */
  applyAlign() {
    const t = this.tableEl;
    if (!t) return;
    Array.from(t.rows).forEach((tr) => {
      Array.from(tr.cells).forEach((td, c) => {
        td.style.textAlign = this.colAlign[c] || "";
      });
    });
  }

  render() {
    const parsed = parseMdTable(this.source);
    if (parsed) this.cells = parsed;
    this.closeInternalLinkSuggest();
    this.editingCell = null;
    this.loadSizes();
    this.loadAlign();
    this.clearLineSelection();
    this.clearCellSelection();
    this.el.empty();
    this.cellSelBox = null; // detached with the old root; recreated on demand
    // Fresh markdown host: unload the previous render's child components (the
    // old cell DOM is about to be discarded by empty()) and start a new one.
    if (this.mdComponent) this.mdComponent.unload();
    this.mdComponent = new Component();
    this.mdComponent.load();
    this.el.addClass("tk-block");
    this.readOnly = this.isReadingView();
    this.el.toggleClass("cp-table-readonly", this.readOnly);

    const scroll = this.el.createDiv({ cls: "cp-table-scroll" });
    const root = (this.rootEl = scroll.createDiv({ cls: "cp-table-root" }));
    const table = (this.tableEl = root.createEl("table", { cls: "cp-table" }));
    const colgroup = table.createEl("colgroup");
    for (let c = 0; c < this.cells[0].length; c++) colgroup.createEl("col");

    this.cells.forEach((row, r) => {
      const tr = table.createEl("tr");
      row.forEach((cellText, c) => {
        const td = tr.createEl("td");
        this.bindCell(td, r, c, cellText);
      });
    });
    this.applySizes();
    this.applyAlign();

    // Reading view: static table only. Cells are rendered above with no edit
    // listeners (see bindCell); skip all the interactive chrome below.
    if (this.readOnly) return;

    this.addColEl = root.createDiv({ cls: "cp-table-add cp-table-add-col", attr: { "aria-label": "Add column" } });
    setIcon(this.addColEl, "plus");
    this.addColEl.addEventListener("pointerdown", (e) => {
      e.stopPropagation();
      e.preventDefault();
      this.flushEdit();
      this.cells.forEach((row) => row.push(""));
      // Page-width mode: take half of the new column's width from the last
      // existing column so only the adjacent column adjusts, not all of them.
      if (this.pageWidth && this.colW.length) {
        const last = this.colW.length - 1;
        const half = Math.round(TABLE_CELL_W / 2);
        this.colW[last] = Math.max(MIN_W, this.colW[last] - half);
      }
      this.colW.push(TABLE_CELL_W);
      this.colAlign.push(null);
      this.save();
    });

    this.addRowEl = this.el.createDiv({ cls: "cp-table-add cp-table-add-row", attr: { "aria-label": "Add row" } });
    setIcon(this.addRowEl, "plus");
    this.addRowEl.addEventListener("pointerdown", (e) => {
      e.stopPropagation();
      e.preventDefault();
      this.flushEdit();
      this.cells.push(this.cells[0].map(() => ""));
      this.rowH.push(TABLE_CELL_H);
      this.save();
    });

    const cols = this.cells[0].length;
    const rows = this.cells.length;
    this.colHandles = [];
    this.rowHandles = [];
    this.colDividers = [];
    this.rowDividers = [];
    // A divider sits on every column's right edge and every row's bottom edge —
    // including the last column and last row, so the rightmost/bottommost borders
    // are resizable too (previously impossible).
    for (let c = 0; c < cols; c++) {
      const h = root.createDiv({ cls: "cp-table-handle cp-table-handle-col", attr: { "aria-label": "Drag to reorder column" } });
      this.bindReorder(h, "col", c);
      this.colHandles.push(h);
      const d = root.createDiv({ cls: "cp-table-divider cp-table-divider-col" });
      this.bindResize(d, "col", c);
      this.colDividers.push(d);
    }
    for (let r = 0; r < rows; r++) {
      const h = root.createDiv({ cls: "cp-table-handle cp-table-handle-row", attr: { "aria-label": "Drag to reorder row" } });
      this.bindReorder(h, "row", r);
      this.rowHandles.push(h);
      const d = root.createDiv({ cls: "cp-table-divider cp-table-divider-row" });
      this.bindResize(d, "row", r);
      this.rowDividers.push(d);
    }

    this.insertColDots = [];
    this.insertRowDots = [];
    this.insertLineEl = root.createDiv({ cls: "cp-insert-line" });
    this.insertLineEl.hide();
    for (let c = 0; c < cols - 1; c++) {
      const dot = root.createDiv({ cls: "cp-insert cp-insert-col", attr: { "aria-label": "Insert column here" } });
      setIcon(dot, "plus");
      this.bindInsert(dot, "col", c);
      this.insertColDots.push(dot);
    }
    for (let r = 0; r < rows - 1; r++) {
      const dot = root.createDiv({ cls: "cp-insert cp-insert-row", attr: { "aria-label": "Insert row here" } });
      setIcon(dot, "plus");
      this.bindInsert(dot, "row", r);
      this.insertRowDots.push(dot);
    }

    // Delete-table button: sits at the block's top-right next to Obsidian's
    // "edit this block" control and is styled like a standard clickable icon
    // (grey bin, grey hover fill). Lives on the block el, not the table chrome.
    this.deleteTableEl = this.el.createDiv({
      cls: "cp-delete-block clickable-icon",
      attr: { "aria-label": "Delete table" }
    });
    setIcon(this.deleteTableEl, "trash-2");
    this.deleteTableEl.addEventListener("pointerdown", (e) => {
      if (e.button !== 0) return;
      e.stopPropagation();
      e.preventDefault();
      this.deleteTable();
    });

    // Page-width toggle: stretches table to fill content width
    this.pageWidthBtn = this.el.createDiv({
      cls: "cp-page-width-btn clickable-icon",
      attr: { "aria-label": "Fit table to page width" }
    });
    setIcon(this.pageWidthBtn, "maximize-2");
    if (this.pageWidth) {
      this.pageWidthBtn.addClass("is-active");
      this.rootEl.addClass("cp-table-fit-page");
      this._updateLastDivider();
    }
    this.pageWidthBtn.addEventListener("pointerdown", (e) => {
      if (e.button !== 0) return;
      e.stopPropagation();
      e.preventDefault();
      this.togglePageWidth();
    });

    this.bindChromeTracker();
    this.hideChrome();
    // Reposition the chrome whenever the table's geometry changes — e.g. when
    // the user switches themes (different cell padding/fonts reflow the table),
    // web fonts finish loading, or the container resizes. Without this the
    // handles/dividers stay pinned to the old layout and drift out of line.
    if (this.resizeObs) this.resizeObs.disconnect();
    this.resizeObs = new ResizeObserver(() => this.layout());
    this.resizeObs.observe(this.tableEl);
    window.requestAnimationFrame(() => this.layout());
    // Restore horizontal scroll position that was captured in save() before
    // the re-render.  Without this the table always snaps to column 0.
    if (this.plugin._btPendingScroll !== undefined) {
      const sl = this.plugin._btPendingScroll;
      delete this.plugin._btPendingScroll;
      const scrollEl = this.el.querySelector(".cp-table-scroll");
      if (scrollEl) requestAnimationFrame(() => { scrollEl.scrollLeft = sl; });
    }
    // Return keyboard focus to the underlying editor (if it is a PM-based
    // view) so Ctrl+Z / Ctrl+Shift+Z are captured by the editor's keymap
    // after every render cycle.
    this.focusEditor();
  }

  // --- proximity-based chrome visibility ---
  bindChromeTracker() {
    // Track on the block element so the add-row button (which lives outside
    // .cp-table-root) is included in the proximity zone.
    const el = this.el;
    if (!el) return;
    el.addEventListener("pointermove", (e) => this.updateChrome(e));
    el.addEventListener("pointerleave", () => {
      if (!this.isEditing()) this.hideChrome();
    });
  }

  updateChrome(e) {
    const t = this.tableEl;
    if (!t || !t.isConnected) return;
    const rect = t.getBoundingClientRect();
    const M = 16;
    if (e.clientX < rect.left - M || e.clientX > rect.right + M || e.clientY < rect.top - M || e.clientY > rect.bottom + M) {
      this.hideChrome();
      return;
    }
    const x = Math.min(Math.max(e.clientX, rect.left + 1), rect.right - 1);
    let c = 0;
    let r = 0;
    const first = t.rows[0];
    for (let i = 0; i < ((first && first.cells.length) || 0); i++) {
      const cr = first.cells[i].getBoundingClientRect();
      if (x >= cr.left && x <= cr.right) {
        c = i;
        break;
      }
    }
    // Pointer below the table → treat as hovering the last row so the
    // add-row button (which sits in the gap) stays visible.
    if (e.clientY >= rect.bottom) {
      r = this.cells.length - 1;
    } else {
      const y = Math.min(Math.max(e.clientY, rect.top + 1), rect.bottom - 1);
      for (let i = 0; i < t.rows.length; i++) {
        const rr = t.rows[i].getBoundingClientRect();
        if (y >= rr.top && y <= rr.bottom) {
          r = i;
          break;
        }
      }
    }
    const cols = this.cells[0].length;
    const rows = this.cells.length;
    this.colHandles.forEach((h, i) => h.toggleClass("is-visible", i === c));
    this.rowHandles.forEach((h, i) => h.toggleClass("is-visible", i === r));
    this.addColEl && this.addColEl.toggleClass("is-visible", c === cols - 1);
    this.addRowEl && this.addRowEl.toggleClass("is-visible", r === rows - 1);
    this.insertColDots.forEach((d, i) => d.toggleClass("is-visible", i === c - 1 || i === c));
    this.insertRowDots.forEach((d, i) => d.toggleClass("is-visible", i === r - 1 || i === r));
  }

  hideChrome() {
    const all = [...this.colHandles, ...this.rowHandles, ...this.insertColDots, ...this.insertRowDots];
    if (this.addColEl) all.push(this.addColEl);
    if (this.addRowEl) all.push(this.addRowEl);
    for (const el of all) el.removeClass("is-visible");
    this.insertLineEl && this.insertLineEl.hide();
  }

  // --- insert between rows/columns ---
  bindInsert(dot, axis, boundary) {
    dot.addEventListener("pointerenter", () => this.showInsertLine(axis, boundary));
    dot.addEventListener("pointerleave", () => this.insertLineEl && this.insertLineEl.hide());
    dot.addEventListener("pointerdown", (e) => {
      if (e.button !== 0) return;
      e.stopPropagation();
      e.preventDefault();
      this.flushEdit();
      this.insertLineEl && this.insertLineEl.hide();
      if (axis === "col") {
        this.cells.forEach((row) => row.splice(boundary + 1, 0, ""));
        this.colW.splice(boundary + 1, 0, TABLE_CELL_W);
        this.colAlign.splice(boundary + 1, 0, null);
        // Page-width mode: take half of the new column's width from each
        // adjacent column so only those two adjust, not the whole table.
        if (this.pageWidth) {
          const half = Math.round(TABLE_CELL_W / 2);
          this.colW[boundary] = Math.max(MIN_W, this.colW[boundary] - half);
          const rightIdx = boundary + 2;
          if (rightIdx < this.colW.length)
            this.colW[rightIdx] = Math.max(MIN_W, this.colW[rightIdx] - half);
        }
      } else {
        this.cells.splice(boundary + 1, 0, this.cells[0].map(() => ""));
        this.rowH.splice(boundary + 1, 0, TABLE_CELL_H);
      }
      this.save();
    });
  }

  showInsertLine(axis, boundary) {
    const t = this.tableEl;
    const line = this.insertLineEl;
    if (!t || !line) return;
    if (axis === "col") {
      const cell = t.rows[0] && t.rows[0].cells[boundary];
      if (!cell) return;
      line.style.left = `${cell.offsetLeft + cell.offsetWidth - 1.5}px`;
      line.style.top = "0px";
      line.style.width = "3px";
      line.style.height = `${t.offsetHeight}px`;
    } else {
      const tr = t.rows[boundary];
      if (!tr) return;
      line.style.top = `${tr.offsetTop + tr.offsetHeight - 1.5}px`;
      line.style.left = "0px";
      line.style.height = "3px";
      line.style.width = `${t.offsetWidth}px`;
    }
    line.show();
  }

  /** Toggle the table between pixel-width and page-fill modes. */
  togglePageWidth() {
    this.pageWidth = !this.pageWidth;
    if (this.pageWidthBtn) this.pageWidthBtn.toggleClass("is-active", this.pageWidth);
    if (this.rootEl) this.rootEl.toggleClass("cp-table-fit-page", this.pageWidth);
    // The rightmost column divider is anchored in page-width mode — the table
    // width is fixed at 100 %, so that edge can't move.
    this._updateLastDivider();
    this.applySizes();
    window.requestAnimationFrame(() => this.layout());
    this.dirty = true;
    this.save();
  }

  /** Disable the last column divider when page-width mode is on. */
  _updateLastDivider() {
    if (!this.colDividers.length) return;
    const last = this.colDividers[this.colDividers.length - 1];
    last.style.cursor = this.pageWidth ? "default" : "";
    last.style.pointerEvents = this.pageWidth ? "none" : "";
  }

  // --- sizing ---
  applySizes() {
    const t = this.tableEl;
    if (!t) return;
    if (this.pageWidth) {
      const total = sumArr(this.colW);
      t.querySelectorAll("col").forEach((c, i) => {
        const pct = total > 0 ? ((this.colW[i] / total) * 100).toFixed(4) : (100 / this.colW.length).toFixed(4);
        c.style.width = `${pct}%`;
      });
      t.style.width = "";
    } else {
      t.querySelectorAll("col").forEach((c, i) => {
        c.style.width = `${this.colW[i] || TABLE_CELL_W}px`;
      });
      t.style.width = `${sumArr(this.colW)}px`;
    }
    Array.from(t.rows).forEach((tr, r) => {
      tr.style.height = `${this.rowH[r] || TABLE_CELL_H}px`;
    });
  }

  /** Position the +/reorder/divider chrome from measured cell geometry. */
  layout() {
    const t = this.tableEl;
    if (!t || !t.isConnected) return;
    if (this.cellSel) this.positionCellSelBox();
    const tw = t.offsetWidth;
    const th = t.offsetHeight;
    if (this.addColEl) {
      this.addColEl.style.left = `${tw + 6}px`;
      this.addColEl.style.top = "0px";
      this.addColEl.style.height = `${th}px`;
    }
    if (this.addRowEl) {
      // addRowEl lives on .tk-block (outside the scroll container) so it
      // stays centred in the viewport regardless of horizontal scroll.
      // Top = scroll padding (24px) + table height + 6px gap.
      this.addRowEl.style.top = `${24 + th + 6}px`;
      this.addRowEl.style.left = "50%";
      this.addRowEl.style.transform = "translateX(-50%)";
    }
    const first = t.rows[0];
    this.colHandles.forEach((h, i) => {
      const cell = first && first.cells[i];
      if (cell) h.style.left = `${cell.offsetLeft + cell.offsetWidth / 2}px`;
    });
    this.colDividers.forEach((d, i) => {
      const cell = first && first.cells[i];
      if (cell) {
        d.style.left = `${cell.offsetLeft + cell.offsetWidth - 3}px`;
        d.style.top = "0px";
        d.style.height = `${th}px`;
      }
    });
    this.rowHandles.forEach((h, r) => {
      const tr = t.rows[r];
      if (tr) h.style.top = `${tr.offsetTop + tr.offsetHeight / 2}px`;
    });
    this.rowDividers.forEach((d, r) => {
      const tr = t.rows[r];
      if (tr) {
        d.style.top = `${tr.offsetTop + tr.offsetHeight - 3}px`;
        d.style.left = "0px";
        d.style.width = `${tw}px`;
      }
    });
    this.insertColDots.forEach((d, i) => {
      const cell = first && first.cells[i];
      if (cell) {
        d.style.left = `${cell.offsetLeft + cell.offsetWidth}px`;
        d.style.top = "-12px";
      }
    });
    this.insertRowDots.forEach((d, r) => {
      const tr = t.rows[r];
      if (tr) {
        d.style.top = `${tr.offsetTop + tr.offsetHeight}px`;
        d.style.left = "-12px";
      }
    });
  }
  /** Drag a divider to resize the column left of / row above it. */
  bindResize(div, axis, index) {
    div.addEventListener("pointerdown", (e) => {
      if (e.button !== 0) return;
      e.stopPropagation();
      e.preventDefault();
      div.setPointerCapture(e.pointerId);
      div.addClass("is-resizing");
      const startX = e.clientX;
      const startY = e.clientY;
      const startSize = axis === "col" ? this.colW[index] : this.rowH[index];

      const onMove = (ev) => {
        // In page-width mode the rightmost divider is anchored — the table
        // width is fixed at 100 % of the container, so it can't move.
        if (axis === "col" && this.pageWidth && index === this.colW.length - 1) return;
        if (axis === "col") {
          this.colW[index] = Math.max(MIN_W, Math.round(startSize + (ev.clientX - startX)));
        } else {
          this.rowH[index] = Math.max(MIN_H, Math.round(startSize + (ev.clientY - startY)));
        }
        // Don't touch the DOM while dragging — even applySizes() forces a
        // full table re-layout on every frame.  Instead show a lightweight
        // indicator line; the real update happens once on pointerup.
        if (this.insertLineEl) {
          const rr = this.rootEl.getBoundingClientRect();
          if (axis === "col") {
            this.insertLineEl.style.left = `${ev.clientX - rr.left}px`;
            this.insertLineEl.style.top = "0px";
            this.insertLineEl.style.width = "2px";
            this.insertLineEl.style.height = `${this.tableEl.offsetHeight}px`;
          } else {
            this.insertLineEl.style.top = `${ev.clientY - rr.top}px`;
            this.insertLineEl.style.left = "0px";
            this.insertLineEl.style.height = "2px";
            this.insertLineEl.style.width = `${this.tableEl.offsetWidth}px`;
          }
          this.insertLineEl.show();
        }
      };

      const onUp = () => {
        div.removeEventListener("pointermove", onMove);
        this.insertLineEl && this.insertLineEl.hide();
        // Now commit: update the model to reflect the final position, apply
        // sizes + layout once, and persist.
        if (axis === "col") {
          // Re-apply with adjacent-column logic for page-width mode
          const finalSize = this.colW[index];
          this.colW[index] = startSize; // reset to drag-start value
          const delta = finalSize - startSize;
          if (this.pageWidth) {
            const adjIdx = index + 1 < this.colW.length ? index + 1 : index - 1;
            if (adjIdx >= 0) {
              const maxShrink = this.colW[adjIdx] - MIN_W;
              const clamped = delta > maxShrink ? maxShrink : delta;
              this.colW[index] = startSize + clamped;
              this.colW[adjIdx] -= clamped;
            } else {
              this.colW[index] = finalSize;
            }
          } else {
            this.colW[index] = finalSize;
          }
        }
        this.applySizes();
        this.layout();
        div.removeClass("is-resizing");
        this.save();
      };

      div.addEventListener("pointermove", onMove);
      div.addEventListener("pointerup", onUp, { once: true });
    });
  }
  async renderCellMarkdown(td, text) {
    td._btRawText = text;
    td._btRenderVersion = (td._btRenderVersion || 0) + 1;
    const version = td._btRenderVersion;
    td.empty();
    if (!text) return;

    const target = td.createDiv({ cls: "cp-cell-markdown" });
    try {
      const owner = this.mdComponent || this.plugin;
      if (MarkdownRenderer.render) {
        await MarkdownRenderer.render(this.plugin.app, text, target, this.ctx.sourcePath || "", owner);
      } else {
        await MarkdownRenderer.renderMarkdown(text, target, this.ctx.sourcePath || "", owner);
      }
      if (td._btRenderVersion !== version || this.editingCell === td) return;
      this.layout();
    } catch (err) {
      console.error("Better Tables: cell markdown render failed", err);
      if (td._btRenderVersion === version && this.editingCell !== td) td.setText(text);
    }
  }

  /** Wire up a freshly created <td>: its text, header style, and the
   *  click-to-edit / re-layout-on-input listeners. Shared by render() and
   *  appendRowAndEdit() so both build identical cells. */
  bindCell(td, r, c, text) {
    this.renderCellMarkdown(td, text);
    if (r === 0) td.addClass("cp-table-header");
    // Reading view: display-only cell, no editing/selection/align listeners.
    if (this.readOnly) return;
    // Use mousedown (not pointerdown): CodeMirror manages focus on mousedown,
    // so this is the event we must intercept to stop the editor from yanking
    // focus back out of the cell — which was eating the first Tab/Enter.
    td.addEventListener("mousedown", (e) => {
      if (e.button !== 0) return;
      if ((e.metaKey || e.ctrlKey) && e.target && e.target.closest && e.target.closest("a")) return;
      // Already editing this cell: leave the event alone so native caret
      // placement and drag-to-select-text work.
      if (this.editingCell === td) return;
      e.preventDefault();
      e.stopPropagation();
      // Editing a DIFFERENT cell: commit that edit first, then treat this press
      // normally (click → select the cell, drag → select a range).
      if (this.editingCell) this.finishEditing();
      // Shift+click with an existing selection: extend it from its anchor to
      // this cell (spreadsheet behavior) instead of starting over.
      if (e.shiftKey && this.cellSel) {
        this.updateCellSelection(r, c);
        return;
      }
      // A press here is ambiguous: a click selects the cell, a drag selects a
      // range of cells. beginCellPointer resolves it on move/up.
      this.beginCellPointer(td, r, c, e);
      // After this interaction (which does not enter edit mode), return keyboard
      // focus to the underlying editor so Ctrl+Z and other shortcuts work. The
      // mousedown stopPropagation above prevented the editor from claiming focus
      // naturally, but without this the PM keymap never sees Ctrl+Z.
      if (!this.editingCell) this.focusEditor();
    });
    td.addEventListener("input", () => {
      this.refreshInternalLinkSuggest(td);
      window.requestAnimationFrame(() => this.layout());
    });
    // Right-click a cell → set its column's text alignment (markdown only
    // supports per-column alignment, so this applies to the whole column).
    td.addEventListener("contextmenu", (e) => {
      if (this.editingCell) {
        // A cell is being edited → Obsidian shows its native editor menu. Flag
        // the column so the editor-menu hook can append Align to that menu
        // (rather than us suppressing the native Cut/Copy/Paste).
        this.plugin.pendingAlign = { widget: this, col: c, at: Date.now() };
        return;
      }
      e.preventDefault();
      e.stopPropagation();
      // Capture selection data NOW (before the menu click clears cellSel via
      // cellSelOutside). The menu click fires pointerdown on the menu element
      // which is outside rootEl, triggering clearCellSelection.
      var hasSel = this.cellInSelection(r, c);
      var selData = null;
      if (hasSel && this.cellSel) {
        var rect = this.selRect();
        selData = {
          rA: rect.rA, rB: rect.rB, cA: rect.cA, cB: rect.cB,
          cols: [] 
        };
        for (var ci = rect.cA; ci <= rect.cB; ci++) selData.cols.push(ci);
      }
      var capturedR = r, capturedC = c;
      var self2 = this;
      const menu = new Menu();
      var cols = [c];
      if (hasSel && selData) {
        cols = selData.cols;
        menu.addItem(function(i) { return i.setTitle("Copy").setIcon("copy").onClick(function() { self2._copyCellsFromRect(selData.rA, selData.rB, selData.cA, selData.cB); }); });
        menu.addItem(function(i) { return i.setTitle("Clear contents").setIcon("eraser").onClick(function() { self2._clearCellsFromRect(selData.rA, selData.rB, selData.cA, selData.cB); }); });
        menu.addSeparator();
      } else {
        menu.addItem(function(i) { return i.setTitle("Copy").setIcon("copy").onClick(function() { self2._copyToClipboard(self2.cells[capturedR][capturedC] || ""); }); });
      }
      menu.addItem(function(i) {
        return i.setTitle("Paste").setIcon("clipboard-paste").onClick(function() { self2.pasteIntoCell(capturedR, capturedC); });
      });
      menu.addSeparator();
      this.addAlignItems(menu, cols);
      menu.showAtMouseEvent(e);
    });
  }

  /** Append the three column-alignment items to a menu. Shared by our own
   *  right-click menu and the injected entries in Obsidian's editor menu. */
  addAlignItems(menu, cols) {
    const list = Array.isArray(cols) ? cols : [cols];
    // Show a checkmark only when every targeted column shares that alignment.
    const allAre = (val) => list.every((c) => (this.colAlign[c] || "left") === val);
    [
      ["Align left", "align-left", "left"],
      ["Align center", "align-center", "center"],
      ["Align right", "align-right", "right"]
    ].forEach(([title, icon, val]) => {
      menu.addItem((i) =>
        i
          .setTitle(title)
          .setIcon(icon)
          .setChecked(allAre(val))
          .onClick(() => this.setColAlign(list, val))
      );
    });
  }

  /** Set a column's alignment and persist. "left" is the markdown default, so
   *  it's stored as null (a plain --- separator). */
  setColAlign(cols, val) {
    this.flushEdit();
    const list = Array.isArray(cols) ? cols : [cols];
    list.forEach((c) => {
      this.colAlign[c] = val === "left" ? null : val;
    });
    this.applyAlign();
    this.dirty = true;
    this.save();
  }

  // --- cell range selection (drag across cells) ---
  /** Resolve a press on a cell into either a click (edit) or a drag (select a
   *  rectangular block of cells). */
  beginCellPointer(startTd, r0, c0, downEvt) {
    // Spreadsheet model: a click SELECTS the cell; clicking again on the cell
    // that's already the sole selection is what enters edit mode. Capture that
    // "was already selected" state before clearing, so the mouseup can decide.
    const wasSelected =
      this.cellSel &&
      this.cellSel.r0 === r0 &&
      this.cellSel.c0 === c0 &&
      this.cellSel.r1 === r0 &&
      this.cellSel.c1 === c0;
    this.clearCellSelection();
    const startX = downEvt.clientX;
    const startY = downEvt.clientY;
    let dragging = false;
    const onMove = (ev) => {
      if (!dragging) {
        if (Math.hypot(ev.clientX - startX, ev.clientY - startY) < 4) return;
        dragging = true;
        this.finishEditing();
        this.clearLineSelection();
        this.beginCellSelection(r0, c0);
      }
      const cell = this.cellAtPoint(ev.clientX, ev.clientY);
      if (cell) this.updateCellSelection(cell.r, cell.c);
    };
    const onUp = (ev) => {
      this.doc.removeEventListener("mousemove", onMove, true);
      this.doc.removeEventListener("mouseup", onUp, true);
      if (dragging) return; // selection stays
      // In two-step mode (default), the first click only selects; editing needs
      // a second click on the already-selected cell. In quick-edit mode a single
      // click edits straight away.
      if (!this.plugin.settings.quickEdit && !wasSelected) {
        this.clearLineSelection();
        this.beginCellSelection(r0, c0);
        return;
      }
      // Edit the cell, caret at the click point.
      this.editCell(startTd, r0, c0, false);
      const range = this.doc.caretRangeFromPoint && this.doc.caretRangeFromPoint(ev.clientX, ev.clientY);
      if (range) {
        const sel = window.getSelection();
        sel && sel.removeAllRanges();
        sel && sel.addRange(range);
      }
    };
    this.doc.addEventListener("mousemove", onMove, true);
    this.doc.addEventListener("mouseup", onUp, true);
  }

  /** Hit-test a viewport point to the cell under it, or null. */
  cellAtPoint(x, y) {
    const t = this.tableEl;
    if (!t) return null;
    for (let ri = 0; ri < t.rows.length; ri++) {
      const row = t.rows[ri];
      for (let ci = 0; ci < row.cells.length; ci++) {
        const rect = row.cells[ci].getBoundingClientRect();
        if (x >= rect.left && x <= rect.right && y >= rect.top && y <= rect.bottom) return { r: ri, c: ci };
      }
    }
    return null;
  }

  beginCellSelection(r0, c0) {
    this.cellSel = { r0, c0, r1: r0, c1: c0 };
    this.highlightCellSelection();
    this.cellSelOutside = (ev) => {
      if (!this.rootEl || !this.rootEl.contains(ev.target)) this.clearCellSelection();
    };
    this.doc.addEventListener("pointerdown", this.cellSelOutside, true);
    this.cellSelKey = (ev) => {
      if (this.isEditing() || !this.cellSel) return;
      if (ev.key === "Delete" || ev.key === "Backspace") {
        ev.preventDefault();
        ev.stopPropagation();
        this.clearSelectedCells();
      } else if (ev.key === "Escape") {
        this.clearCellSelection();
      } else if ((ev.metaKey || ev.ctrlKey) && (ev.key === "c" || ev.key === "C")) {
        ev.preventDefault();
        ev.stopPropagation();
        this.copyCellSelection();
      } else if ((ev.metaKey || ev.ctrlKey) && (ev.key === "v" || ev.key === "V")) {
        // Ctrl+V on selected cell(s): paste into the anchor cell
        ev.preventDefault();
        ev.stopPropagation();
        var self5 = this;
        var r0 = this.cellSel.r0, c0 = this.cellSel.c0;
        self5.pasteIntoCell(r0, c0);
      } else if (ev.key === "Enter" || ev.key === "F2") {
        // Edit the selection's anchor cell, caret at the end.
        ev.preventDefault();
        ev.stopPropagation();
        const { r0, c0 } = this.cellSel;
        const td = this.tableEl.rows[r0] && this.tableEl.rows[r0].cells[c0];
        if (td) this.editCell(td, r0, c0, true);
      } else if (ev.key.length === 1 && !ev.metaKey && !ev.ctrlKey && !ev.altKey) {
        // Type-to-edit: typing on a selected cell starts editing and REPLACES
        // its content (spreadsheet behavior). Empty the cell and let the
        // browser's default insertion type the character — that way the caret
        // naturally lands after it (manually placing the caret raced with
        // focus and left it before the first letter).
        ev.stopPropagation();
        const { r0, c0 } = this.cellSel;
        const td = this.tableEl.rows[r0] && this.tableEl.rows[r0].cells[c0];
        if (!td) return;
        this.editCell(td, r0, c0, true);
        td.setText("");
      }
    };
    this.doc.addEventListener("keydown", this.cellSelKey, true);
  }

  updateCellSelection(r1, c1) {
    if (!this.cellSel) return;
    if (this.cellSel.r1 === r1 && this.cellSel.c1 === c1) return;
    this.cellSel.r1 = r1;
    this.cellSel.c1 = c1;
    this.highlightCellSelection();
  }

  /** Normalized {rA,rB,cA,cB} bounds of the current cell selection. */
  selRect() {
    const { r0, c0, r1, c1 } = this.cellSel;
    return {
      rA: Math.min(r0, r1),
      rB: Math.max(r0, r1),
      cA: Math.min(c0, c1),
      cB: Math.max(c0, c1)
    };
  }

  highlightCellSelection() {
    const t = this.tableEl;
    if (!t) return;
    t.querySelectorAll("td.cp-cell-selected").forEach((td) => td.removeClass("cp-cell-selected"));
    if (!this.cellSel) {
      this.positionCellSelBox();
      return;
    }
    const { rA, rB, cA, cB } = this.selRect();
    for (let ri = rA; ri <= rB; ri++) {
      for (let ci = cA; ci <= cB; ci++) {
        const cell = t.rows[ri] && t.rows[ri].cells[ci];
        if (cell) cell.addClass("cp-cell-selected");
      }
    }
    this.positionCellSelBox();
  }

  /** Draw the selection outline as one overlay rectangle above the grid, so the
   *  cells' own borders can't paint over it (an inset box-shadow would sit under
   *  those borders). Sized from the block's corner cells. */
  positionCellSelBox() {
    if (!this.cellSel) {
      if (this.cellSelBox) this.cellSelBox.style.display = "none";
      return;
    }
    const t = this.tableEl;
    if (!t) return;
    if (!this.cellSelBox) {
      this.cellSelBox = this.rootEl.createDiv({ cls: "cp-cell-selbox" });
    }
    const { rA, rB, cA, cB } = this.selRect();
    const a = t.rows[rA] && t.rows[rA].cells[cA];
    const b = t.rows[rB] && t.rows[rB].cells[cB];
    if (!a || !b) {
      this.cellSelBox.style.display = "none";
      return;
    }
    this.cellSelBox.style.display = "block";
    this.cellSelBox.style.left = `${a.offsetLeft}px`;
    this.cellSelBox.style.top = `${a.offsetTop}px`;
    this.cellSelBox.style.width = `${b.offsetLeft + b.offsetWidth - a.offsetLeft}px`;
    this.cellSelBox.style.height = `${b.offsetTop + b.offsetHeight - a.offsetTop}px`;
  }

  clearCellSelection() {
    if (this.tableEl) {
      this.tableEl.querySelectorAll("td.cp-cell-selected").forEach((td) => td.removeClass("cp-cell-selected"));
    }
    this.cellSel = null;
    if (this.cellSelBox) this.cellSelBox.style.display = "none";
    if (this.cellSelOutside) {
      this.doc.removeEventListener("pointerdown", this.cellSelOutside, true);
      this.cellSelOutside = null;
    }
    if (this.cellSelKey) {
      this.doc.removeEventListener("keydown", this.cellSelKey, true);
      this.cellSelKey = null;
    }
  }

  /** Empty every cell in the selection, then persist. */
  clearSelectedCells() {
    if (!this.cellSel) return;
    const { rA, rB, cA, cB } = this.selRect();
    let changed = false;
    for (let ri = rA; ri <= rB; ri++) {
      for (let ci = cA; ci <= cB; ci++) {
        if (this.cells[ri][ci] !== "") {
          this.cells[ri][ci] = "";
          changed = true;
        }
      }
    }
    // Clear first so this widget's doc listeners are removed before save()
    // re-renders the block into a fresh widget.
    this.clearCellSelection();
    if (changed) {
      this.dirty = true;
      this.save();
    }
  }

  /** Copy cells in a rectangle to clipboard. Doesn't depend on this.cellSel. */
  _copyCellsFromRect(rA, rB, cA, cB) {
    var lines = [];
    for (var ri = rA; ri <= rB; ri++) {
      var row = [];
      for (var ci = cA; ci <= cB; ci++) row.push(this.cells[ri][ci]);
      lines.push(row.join("\t"));
    }
    this._copyToClipboard(lines.join("\n"));
  }

  /** Clear cells in a rectangle. Doesn't depend on this.cellSel. */
  _clearCellsFromRect(rA, rB, cA, cB) {
    var changed = false;
    for (var ri = rA; ri <= rB; ri++) {
      for (var ci = cA; ci <= cB; ci++) {
        if (this.cells[ri][ci] !== "") { this.cells[ri][ci] = ""; changed = true; }
      }
    }
    if (changed) { this.dirty = true; this.save(); }
  }

  /** Copy the selection to the clipboard as tab-separated rows. */
  copyCellSelection() {
    console.log("BT copyCellSelection called, cellSel=", this.cellSel);
    if (!this.cellSel) return;
    const { rA, rB, cA, cB } = this.selRect();
    const lines = [];
    for (let ri = rA; ri <= rB; ri++) {
      const row = [];
      for (let ci = cA; ci <= cB; ci++) row.push(this.cells[ri][ci]);
      lines.push(row.join("\t"));
    }
    this._copyToClipboard(lines.join("\n"));
  }

  /** Paste clipboard text at cursor in an editing cell. Called from keydown. */
  async _pasteAtCursor(td) {
    console.log("BT _pasteAtCursor called, td=", td && td.textContent && td.textContent.substring(0,20));
    try {
      var text = await navigator.clipboard.readText();
      console.log("BT _pasteAtCursor clipboard text length=", text ? text.length : 0);
      if (text) {
        var ok = this.doc.execCommand("insertText", false, text);
        console.log("BT _pasteAtCursor execCommand insertText=", ok);
        window.requestAnimationFrame(function() { this.layout(); }.bind(this));
      }
    } catch (err) {
      console.error("Better Tables: _pasteAtCursor error", err);
    }
  }

  /** Reliable clipboard write. */
  _copyToClipboard(text) {
    console.log("BT _copyToClipboard called, text length=", text ? text.length : 0, "text=", (text||"").substring(0,30));
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(text).then(function() {
        console.log("BT _copyToClipboard writeText SUCCESS");
        new Notice("Better Tables: cells copied.");
      }).catch(function(e) {
        console.error("BT _copyToClipboard writeText FAILED", e);
        new Notice("Better Tables: copy failed.");
      });
    } else {
      var ta = document.createElement("textarea");
      ta.value = text;
      ta.style.position = "fixed";
      ta.style.left = "-9999px";
      document.body.appendChild(ta);
      ta.select();
      try { document.execCommand("copy"); new Notice("Better Tables: cells copied."); }
      catch (e2) { new Notice("Better Tables: copy failed."); }
      document.body.removeChild(ta);
    }
  }

  /** Copy a single cell's text to clipboard (no selection needed). */
  copyCell(r, c) {
    console.log("BT copyCell called r=", r, "c=", c, "val=", (this.cells[r][c]||"").substring(0,20));
    this._copyToClipboard(this.cells[r][c] || "");
  }

  /** Paste clipboard text into cell(s), splitting tabs/newlines. */
  async pasteIntoCell(r, c) {
    console.log("BT pasteIntoCell called r=", r, "c=", c);
    try {
      var text = await navigator.clipboard.readText();
      console.log("BT pasteIntoCell clipboard text length=", text ? text.length : 0);
      if (!text) return;
      var rawLines = text.split("\n").map(function(l) { return l.charAt(l.length - 1) === "\r" ? l.slice(0, -1) : l; });
      var lines = rawLines.length === 1 ? rawLines : rawLines.filter(function(l) { return l.trim() !== ""; });
      if (!lines.length) return;
      var rows = lines.map(function(l) { return l.split("\t"); });
      var pasteRows = rows.length;
      var pasteCols = Math.max.apply(null, rows.map(function(r) { return r.length; }));
      while (this.cells.length < r + pasteRows) {
        this.cells.push(this.cells[0].map(function() { return ""; }));
        this.rowH.push(TABLE_CELL_H);
      }
      while (this.cells[0].length < c + pasteCols) {
        this.cells.forEach(function(row) { row.push(""); });
        this.colW.push(TABLE_CELL_W);
        this.colAlign.push(null);
      }
      for (var dr = 0; dr < pasteRows; dr++)
        for (var dc = 0; dc < pasteCols; dc++)
          this.cells[r + dr][c + dc] = (rows[dr] && rows[dr][dc]) || "";
      this.dirty = true;
      this.save();
    } catch (err) {
      console.error("Better Tables: paste failed", err);
      new Notice("Better Tables: failed to paste.");
    }
  }

  /** True if (r,c) falls inside the current cell selection. */
  cellInSelection(r, c) {
    if (!this.cellSel) return false;
    const { rA, rB, cA, cB } = this.selRect();
    return r >= rA && r <= rB && c >= cA && c <= cB;
  }

  selectionOffsets(td) {
    const sel = window.getSelection();
    if (!sel || !sel.rangeCount) return null;
    const range = sel.getRangeAt(0);
    if (!td.contains(range.startContainer) || !td.contains(range.endContainer)) return null;
    const pre = range.cloneRange();
    pre.selectNodeContents(td);
    pre.setEnd(range.startContainer, range.startOffset);
    return { start: pre.toString().length, end: pre.toString().length + range.toString().length };
  }

  setCellTextAndCaret(td, text, caret) {
    td.setText(text);
    td.focus();
    const node = td.firstChild || td.appendChild(this.doc.createTextNode(""));
    const pos = Math.max(0, Math.min(caret, node.nodeValue.length));
    const range = this.doc.createRange();
    range.setStart(node, pos);
    range.collapse(true);
    const sel = window.getSelection();
    sel && sel.removeAllRanges();
    sel && sel.addRange(range);
    window.requestAnimationFrame(() => this.layout());
  }

  nativeMarkdownLink(file) {
    const sourcePath = this.ctx.sourcePath || "";
    const fm = this.plugin.app.fileManager;
    if (fm && fm.generateMarkdownLink) return fm.generateMarkdownLink(file, sourcePath);
    return `[[${file.basename}]]`;
  }

  linkTriggerInfo(td) {
    const pos = this.selectionOffsets(td);
    if (!pos || pos.start !== pos.end) return null;
    const text = this.cellText(td);
    const before = text.slice(0, pos.start);
    const start = before.lastIndexOf("[[");
    if (start === -1) return null;
    const query = before.slice(start + 2);
    if (query.includes("]]") || query.includes("\n")) return null;
    if (/[#^|]/.test(query)) return null;
    return { start, end: pos.end, query, text };
  }

  linkSuggestFiles(query) {
    const q = query.trim().toLowerCase();
    const files = this.plugin.app.vault.getFiles ? this.plugin.app.vault.getFiles() : this.plugin.app.vault.getMarkdownFiles();
    const scored = [];
    for (const file of files) {
      const title = file.basename || file.name || file.path;
      const path = file.path || title;
      const hay = `${title}\n${path}`.toLowerCase();
      let score = 0;
      if (!q) score = 1;
      else if (title.toLowerCase() === q) score = 100;
      else if (title.toLowerCase().startsWith(q)) score = 80;
      else if (path.toLowerCase().startsWith(q)) score = 70;
      else if (hay.includes(q)) score = 50;
      else {
        let at = 0;
        for (const ch of q) {
          at = hay.indexOf(ch, at);
          if (at === -1) break;
          at++;
        }
        if (at !== -1) score = 20;
      }
      if (score) scored.push({ file, score, title, path });
    }
    scored.sort((a, b) => b.score - a.score || a.path.localeCompare(b.path));
    return scored.slice(0, MAX_LINK_SUGGESTIONS).map((x) => x.file);
  }

  positionLinkSuggest() {
    if (!this.linkSuggestEl || !this.linkSuggestTd) return;
    const rect = this.linkSuggestTd.getBoundingClientRect();
    const vw = this.doc.defaultView ? this.doc.defaultView.innerWidth : window.innerWidth;
    const vh = this.doc.defaultView ? this.doc.defaultView.innerHeight : window.innerHeight;
    const width = Math.min(Math.max(rect.width, 320), 520, vw - 24);
    const left = Math.max(12, Math.min(rect.left, vw - width - 12));
    const below = rect.bottom + 4;
    const maxHeight = Math.max(160, Math.min(360, vh - below - 12));
    this.linkSuggestEl.style.left = `${left}px`;
    this.linkSuggestEl.style.top = `${below}px`;
    this.linkSuggestEl.style.width = `${width}px`;
    this.linkSuggestEl.style.maxHeight = `${maxHeight}px`;
  }

  renderLinkSuggest(td, info) {
    this.linkSuggestTd = td;
    if (!this.linkSuggestInfo || this.linkSuggestInfo.query !== info.query) this.linkSuggestIndex = 0;
    this.linkSuggestInfo = info;
    this.linkSuggestItems = this.linkSuggestFiles(info.query);
    this.linkSuggestIndex = Math.min(this.linkSuggestIndex || 0, Math.max(0, this.linkSuggestItems.length - 1));

    if (!this.linkSuggestEl) {
      const el = (this.linkSuggestEl = this.doc.body.createDiv({ cls: "suggestion-container better-tables-link-suggest" }));
      el.addEventListener("mousedown", (e) => {
        e.preventDefault();
        e.stopPropagation();
      });
      this.linkSuggestOutside = (ev) => {
        if (ev.target === td || td.contains(ev.target) || el.contains(ev.target)) return;
        this.closeInternalLinkSuggest();
      };
      this.doc.addEventListener("mousedown", this.linkSuggestOutside, true);
    }

    const el = this.linkSuggestEl;
    el.empty();
    this.linkSuggestItems.forEach((file, i) => {
      const item = el.createDiv({ cls: `suggestion-item${i === this.linkSuggestIndex ? " is-selected" : ""}` });
      item.createDiv({ cls: "suggestion-title", text: file.basename || file.name || file.path });
      const folder = (file.parent && file.parent.path && file.parent.path !== "/" ? `${file.parent.path}/` : "") || "";
      item.createDiv({ cls: "suggestion-note", text: folder });
      item.addEventListener("mouseenter", () => {
        this.linkSuggestIndex = i;
        this.renderLinkSuggest(td, this.linkSuggestInfo);
      });
      item.addEventListener("click", () => this.chooseInternalLink(file));
    });
    if (!this.linkSuggestItems.length) el.createDiv({ cls: "suggestion-item is-disabled", text: "No matches" });
    this.positionLinkSuggest();
  }

  refreshInternalLinkSuggest(td) {
    if (this.editingCell !== td) return;
    const info = this.linkTriggerInfo(td);
    if (!info) {
      this.closeInternalLinkSuggest();
      return;
    }
    this.renderLinkSuggest(td, info);
  }

  moveInternalLinkSuggest(dir) {
    if (!this.linkSuggestEl || !this.linkSuggestItems || !this.linkSuggestItems.length) return;
    this.linkSuggestIndex = (this.linkSuggestIndex + dir + this.linkSuggestItems.length) % this.linkSuggestItems.length;
    this.renderLinkSuggest(this.linkSuggestTd, this.linkSuggestInfo);
  }

  chooseInternalLink(file) {
    const td = this.linkSuggestTd;
    const info = td && this.linkTriggerInfo(td);
    if (!td || !info) return;
    const link = this.nativeMarkdownLink(file);
    const text = `${info.text.slice(0, info.start)}${link}${info.text.slice(info.end)}`;
    this.closeInternalLinkSuggest();
    this.setCellTextAndCaret(td, text, info.start + link.length);
  }

  closeInternalLinkSuggest() {
    if (this.linkSuggestOutside) {
      this.doc.removeEventListener("mousedown", this.linkSuggestOutside, true);
      this.linkSuggestOutside = null;
    }
    if (this.linkSuggestEl) {
      this.linkSuggestEl.detach();
      this.linkSuggestEl = null;
    }
    this.linkSuggestTd = null;
    this.linkSuggestInfo = null;
    this.linkSuggestItems = [];
    this.linkSuggestIndex = 0;
  }

  editCell(td, r, c, fromKeyboard) {
    if (this.editingCell === td) return;
    this.clearCellSelection();
    this.finishEditing();
    this.editingCell = td;
    this.editingPos = { r, c };
    td._btRenderVersion = (td._btRenderVersion || 0) + 1;
    td.setText(this.cells[r][c] || "");
    td.contentEditable = "true";
    td.addClass("is-editing-cell");
    // Always take keyboard focus so the cell captures the very first Tab/Enter.
    // Only for keyboard navigation do we drop the caret at the end; for a click
    // the caller (mousedown) places the caret at the clicked point.
    td.focus();
    if (fromKeyboard) {
      const range = this.doc.createRange();
      range.selectNodeContents(td);
      range.collapse(false);
      const sel = window.getSelection();
      sel && sel.removeAllRanges();
      sel && sel.addRange(range);
    }
    // Blur commits and saves — unless the edit was already committed (e.g. by a
    // structural action or keyboard navigation), in which case editingCell has
    // been cleared and this is a no-op so we never issue a racing save.
    const onBlur = () => {
      this.closeInternalLinkSuggest();
      if (this.editingCell === td) this.commitCell(td, r, c, true);
    };
    td.addEventListener("blur", onBlur, { once: true });
    // Bind navigation keys once per cell so repeated edits don't stack handlers
    // (which would double-fire Tab/Enter navigation).
    if (!td._btKeyBound) {
      td._btKeyBound = true;
      td.addEventListener("keydown", (e) => {
        if (this.editingCell !== td) return;
        const mod = e.metaKey || e.ctrlKey;
        if (this.linkSuggestEl) {
          if (e.key === "ArrowDown" || e.key === "ArrowUp") {
            e.preventDefault();
            e.stopPropagation();
            this.moveInternalLinkSuggest(e.key === "ArrowDown" ? 1 : -1);
            return;
          }
          if (e.key === "Enter" || e.key === "Tab") {
            if (this.linkSuggestItems && this.linkSuggestItems.length) {
              e.preventDefault();
              e.stopPropagation();
              this.chooseInternalLink(this.linkSuggestItems[this.linkSuggestIndex || 0]);
              return;
            }
          }
          if (e.key === "Escape") {
            e.preventDefault();
            e.stopPropagation();
            this.closeInternalLinkSuggest();
            return;
          }
        }
        // Cmd/Ctrl+A — select all text in THIS cell (not the whole note).
        if (mod && (e.key === "a" || e.key === "A")) {
          e.preventDefault();
          e.stopPropagation();
          const range = this.doc.createRange();
          range.selectNodeContents(td);
          const sel = window.getSelection();
          sel && sel.removeAllRanges();
          sel && sel.addRange(range);
          return;
        }
        // Cmd/Ctrl+Enter or Shift+Enter — insert a line break inside the cell.
        if ((mod || e.shiftKey) && e.key === "Enter") {
          e.preventDefault();
          e.stopPropagation();
          this.insertLineBreak(td);
          return;
        }
        // Ctrl+V paste: handle ourselves so Obsidian doesn't intercept it.
        if (mod && (e.key === "v" || e.key === "V")) {
          console.log("BT keydown Ctrl+V detected");
          e.preventDefault();
          e.stopPropagation();
          this._pasteAtCursor(td);
          return;
        }
        // Let other standard modifier shortcuts (Ctrl+X cut, Ctrl+C copy,
        // Ctrl+Z undo, etc.) pass through to the browser.
        if (mod && !e.shiftKey) return;
        e.stopPropagation();
        if (e.key === "Escape") {
          e.preventDefault();
          td.blur();
        } else if (e.key === "Tab") {
          e.preventDefault();
          const lastCell = r === this.cells.length - 1 && c === this.cells[0].length - 1;
          // Tab off the bottom-right cell grows the table and continues in the
          // new row's first cell, so you can fill a table without reaching for
          // the mouse.
          if (!e.shiftKey && lastCell) this.appendRowAndEdit(0);
          else this.editNeighbor(r, c, 0, e.shiftKey ? -1 : 1, true);
        } else if (e.key === "Enter") {
          e.preventDefault();
          // Enter on the last row grows the table and keeps editing in the new
          // row, so you can keep typing down the column.
          if (r === this.cells.length - 1) this.appendRowAndEdit(c);
          else this.editNeighbor(r, c, 1, 0);
        } else if (e.key === "ArrowLeft" || e.key === "ArrowRight" || e.key === "ArrowUp" || e.key === "ArrowDown") {
          // Arrows move the caret within the cell until it hits an edge, then
          // step to the adjacent cell.
          const edge = this.getCaretEdges(td);
          if (e.key === "ArrowLeft" && edge.atStart) {
            e.preventDefault();
            this.editNeighbor(r, c, 0, -1);
          } else if (e.key === "ArrowRight" && edge.atEnd) {
            e.preventDefault();
            this.editNeighbor(r, c, 0, 1);
          } else if (e.key === "ArrowUp" && edge.atTop) {
            e.preventDefault();
            this.editNeighbor(r, c, -1, 0);
          } else if (e.key === "ArrowDown" && edge.atBottom) {
            e.preventDefault();
            this.editNeighbor(r, c, 1, 0);
          }
        }
      });
    }
    // Ensure copy from an editing cell writes plain text to the clipboard.
    // (Paste is handled by the keydown handler via _pasteAtCursor.)
    if (!td._btClipboardBound) {
      td._btClipboardBound = true;
      td.addEventListener("copy", (e) => {
        var sel = window.getSelection();
        if (!sel || sel.rangeCount === 0) return;
        var selectedText = sel.toString();
        if (selectedText && e.clipboardData) {
          e.clipboardData.setData("text/plain", selectedText);
        }
      });
    }
  }

  /** Move to an adjacent cell. Commits the current cell into the model WITHOUT
   *  saving (so no file write / re-render happens mid-navigation, which would
   *  tear down the DOM). When `eject` is set, navigating past the table edge
   *  commits + persists and exits; otherwise it's a no-op (stay in the cell). */
  editNeighbor(r, c, dr, dc, eject = false) {
    let nr = r + dr;
    let nc = c + dc;
    if (nc >= this.cells[0].length) {
      nc = 0;
      nr++;
    }
    if (nc < 0) {
      nc = this.cells[0].length - 1;
      nr--;
    }
    const table = this.el.querySelector(".cp-table");
    const td = nr >= 0 && nr < this.cells.length && table && table.rows[nr] && table.rows[nr].cells[nc];
    if (td) {
      this.editCell(td, nr, nc, true);
    } else if (eject) {
      // Navigated past the edge: commit and persist now.
      this.finishEditing();
      if (this.dirty) this.save();
    }
  }

  /** Append a new row to the model and DOM (no file write yet) and start editing
   *  it in the given column, so Enter on the bottom row flows into a fresh row.
   *  The save happens later when editing leaves the table, avoiding a mid-edit
   *  re-render that would drop focus. */
  appendRowAndEdit(col) {
    this.finishEditing();
    const nr = this.cells.length;
    this.cells.push(this.cells[0].map(() => ""));
    this.rowH.push(TABLE_CELL_H);
    this.dirty = true;
    const tr = this.tableEl.createEl("tr");
    this.cells[nr].forEach((text, c) => {
      const td = tr.createEl("td");
      this.bindCell(td, nr, c, text);
    });
    this.applySizes();
    const td = tr.cells[col];
    if (td) this.editCell(td, nr, col, true);
    this.layout();
  }

  /** Whether the caret sits at the start/end of the text and on the first/last
   *  visual line — used to decide when an arrow key should leave the cell. */
  getCaretEdges(td) {
    const sel = window.getSelection();
    if (!sel || !sel.rangeCount) return { atStart: true, atEnd: true, atTop: true, atBottom: true };
    const range = sel.getRangeAt(0);
    const pre = range.cloneRange();
    pre.selectNodeContents(td);
    pre.setEnd(range.startContainer, range.startOffset);
    const atStart = range.collapsed && pre.toString().length === 0;
    const post = range.cloneRange();
    post.selectNodeContents(td);
    post.setStart(range.endContainer, range.endOffset);
    const atEnd = range.collapsed && post.toString().length === 0;
    let atTop = atStart;
    let atBottom = atEnd;
    const caretRect = range.getBoundingClientRect();
    if (caretRect && caretRect.height) {
      const cellRect = td.getBoundingClientRect();
      const lh = parseFloat(getComputedStyle(td).lineHeight) || 18;
      atTop = caretRect.top - cellRect.top < lh * 0.75;
      atBottom = cellRect.bottom - caretRect.bottom < lh * 0.75;
    }
    return { atStart, atEnd, atTop, atBottom };
  }

  /** Insert a hard line break at the caret. Uses a real <br> (a raw "\n" text
   *  node won't render a trailing newline in contentEditable); execCommand
   *  handles the trailing-<br> sentinel so the new line is visible. */
  insertLineBreak(td) {
    const ok = this.doc.execCommand && this.doc.execCommand("insertLineBreak");
    if (!ok) {
      const sel = window.getSelection();
      if (sel && sel.rangeCount) {
        const range = sel.getRangeAt(0);
        range.deleteContents();
        const br = this.doc.createElement("br");
        range.insertNode(br);
        // Sentinel <br> so the line renders when the break is at the very end.
        const tail = this.doc.createElement("br");
        br.after(tail);
        range.setStartBefore(tail);
        range.collapse(true);
        sel.removeAllRanges();
        sel.addRange(range);
      }
    }
    window.requestAnimationFrame(() => this.layout());
  }

  /** Read an edit-mode cell's DOM back to raw text, turning <br> and block
   *  boundaries into newlines (so Cmd/Shift+Enter line breaks round-trip). */
  cellText(td) {
    const parts = [];
    const walk = (node) => {
      node.childNodes.forEach((n) => {
        if (n.nodeType === 3) {
          parts.push(n.nodeValue);
        } else if (n.nodeName === "BR") {
          parts.push("\n");
        } else if (n.nodeName === "DIV" || n.nodeName === "P") {
          if (parts.length && !parts[parts.length - 1].endsWith("\n")) parts.push("\n");
          walk(n);
        } else {
          walk(n);
        }
      });
    };
    walk(td);
    return parts.join("");
  }

  /** Pull the edited text into the model and end edit mode. Does NOT save
   *  unless doSave is set — structural actions flush then issue a single save. */
  commitCell(td, r, c, doSave) {
    // Clear editing state BEFORE disabling contentEditable. Setting
    // contentEditable=false on the focused cell fires a synchronous blur; if
    // editingCell still pointed here, the once-blur handler would re-enter
    // commitCell with doSave=true and trigger a save+re-render mid-navigation
    // (which cancelled the first Tab/Enter).
    if (this.editingCell === td) this.editingCell = null;
    this.editingPos = null;
    this.closeInternalLinkSuggest();
    td.contentEditable = "false";
    td.removeClass("is-editing-cell");
    const v = this.cellText(td).trim();
    if (v !== this.cells[r][c]) {
      this.cells[r][c] = v;
      this.dirty = true;
    }
    this.renderCellMarkdown(td, this.cells[r][c]);
    if (doSave) {
      if (this.dirty) this.save();
      else this.layout();
    } else {
      this.layout();
    }
  }

  /** Commit any in-progress cell edit into the model without saving, so a
   *  following structural change can persist everything in one write. */
  flushEdit() {
    const td = this.editingCell;
    const pos = this.editingPos;
    if (!td || !pos) return;
    this.commitCell(td, pos.r, pos.c, false);
  }

  finishEditing() {
    const td = this.editingCell;
    const pos = this.editingPos;
    if (td && pos) this.commitCell(td, pos.r, pos.c, false);
    this.editingCell = null;
    this.editingPos = null;
  }

  // --- reorder + selection ---
  bindReorder(handle, axis, index) {
    // Right-click on a handle shows a context menu to delete the line.
    // More reliable than the floating delete button, which can end up
    // off-screen when the proximity margin is small.
    handle.addEventListener("contextmenu", (e) => {
      e.preventDefault();
      e.stopPropagation();
      this.clearLineSelection();
      this.clearCellSelection();
      this.selected = { axis, index };
      const handles = axis === "row" ? this.rowHandles : this.colHandles;
      handles[index] && handles[index].addClass("is-selected");
      this.lineCells(axis, index).forEach((td) => td.addClass("cp-line-selected"));
      const menu = new Menu();
      const label = axis === "col" ? "Delete column" : "Delete row";
      const self = this;
      menu.addItem((i) =>
        i
          .setTitle(label)
          .setIcon("trash-2")
          .onClick(() => {
            self.clearLineSelection();
            self.deleteLine(axis, index);
          })
      );
      menu.showAtMouseEvent(e);
    });

    handle.addEventListener("pointerdown", (e) => {
      if (e.button !== 0) return;
      e.stopPropagation();
      e.preventDefault();
      handle.setPointerCapture(e.pointerId);
      const table = this.tableEl;
      if (!table) return;
      const count = axis === "row" ? this.cells.length : this.cells[0].length;
      const startX = e.clientX;
      const startY = e.clientY;
      let dragging = false;
      let ghost = null;
      let target = index;
      const setSrc = (on) => {
        if (axis === "row") {
          table.rows[index] && table.rows[index].toggleClass("cp-drag-src", on);
        } else {
          for (const row of Array.from(table.rows)) row.cells[index] && row.cells[index].toggleClass("cp-drag-src", on);
        }
      };
      const moveGhost = (ev) => {
        if (!ghost) return;
        const rr = this.rootEl.getBoundingClientRect();
        if (axis === "row") {
          ghost.style.left = "0px";
          ghost.style.top = `${ev.clientY - rr.top - ghost.offsetHeight / 2}px`;
        } else {
          ghost.style.top = "0px";
          ghost.style.left = `${ev.clientX - rr.left - ghost.offsetWidth / 2}px`;
        }
      };
      const beginDrag = (ev) => {
        dragging = true;
        this.clearLineSelection();
        handle.addClass("is-dragging");
        ghost = this.makeGhost(axis, index);
        setSrc(true);
        moveGhost(ev);
      };
      const onMove = (ev) => {
        if (!dragging) {
          if (Math.hypot(ev.clientX - startX, ev.clientY - startY) < 4) return;
          beginDrag(ev);
        } else {
          moveGhost(ev);
        }
        const rect = table.getBoundingClientRect();
        const tt = axis === "row" ? (ev.clientY - rect.top) / rect.height : (ev.clientX - rect.left) / rect.width;
        target = Math.max(0, Math.min(count - 1, Math.floor(tt * count)));
        table.querySelectorAll("tr, td").forEach((el) => el.removeClass("cp-drop-target"));
        if (target === index) return;
        if (axis === "row") {
          table.rows[target] && table.rows[target].addClass("cp-drop-target");
        } else {
          for (const row of Array.from(table.rows)) row.cells[target] && row.cells[target].addClass("cp-drop-target");
        }
      };
      const onUp = () => {
        handle.removeEventListener("pointermove", onMove);
        handle.removeEventListener("pointerup", onUp);
        if (!dragging) {
          if (this.selected && this.selected.axis === axis && this.selected.index === index) {
            this.clearLineSelection();
          } else {
            this.selectLine(axis, index);
          }
          return;
        }
        handle.removeClass("is-dragging");
        ghost && ghost.remove();
        setSrc(false);
        if (target !== index) {
          if (axis === "row") {
            const [row] = this.cells.splice(index, 1);
            this.cells.splice(target, 0, row);
            const [h] = this.rowH.splice(index, 1);
            this.rowH.splice(target, 0, h);
          } else {
            for (const row of this.cells) {
              const [cell] = row.splice(index, 1);
              row.splice(target, 0, cell);
            }
            const [w] = this.colW.splice(index, 1);
            this.colW.splice(target, 0, w);
            const [al] = this.colAlign.splice(index, 1);
            this.colAlign.splice(target, 0, al);
          }
          this.save();
        } else {
          this.render();
        }
      };
      handle.addEventListener("pointermove", onMove);
      handle.addEventListener("pointerup", onUp);
    });
  }

  selectLine(axis, index) {
    this.clearLineSelection();
    this.clearCellSelection();
    const table = this.tableEl;
    if (!table) return;
    this.selected = { axis, index };
    const handles = axis === "row" ? this.rowHandles : this.colHandles;
    handles[index] && handles[index].addClass("is-selected");
    this.lineCells(axis, index).forEach((td) => td.addClass("cp-line-selected"));
    this.lineSelKey = (ev) => {
      if ((ev.key === "Delete" || ev.key === "Backspace") && !this.isEditing()) {
        ev.preventDefault();
        ev.stopPropagation();
        this.deleteLine(axis, index);
      } else if (ev.key === "Escape") {
        this.clearLineSelection();
      }
    };
    this.doc.addEventListener("keydown", this.lineSelKey, true);
  }

  lineCells(axis, index) {
    const table = this.tableEl;
    if (!table) return [];
    if (axis === "row") return Array.from((table.rows[index] && table.rows[index].cells) || []);
    return Array.from(table.rows).map((r) => r.cells[index]).filter(Boolean);
  }

  clearLineSelection() {
    if (this.selected) {
      const { axis, index } = this.selected;
      const h = (axis === "row" ? this.rowHandles : this.colHandles)[index];
      h && h.removeClass("is-selected");
      this.lineCells(axis, index).forEach((td) => td.removeClass("cp-line-selected"));
    }
    this.selected = null;
    if (this.lineSelKey) {
      this.doc.removeEventListener("keydown", this.lineSelKey, true);
      this.lineSelKey = null;
    }
  }

  deleteLine(axis, index) {
    const rows = this.cells.length;
    const cols = (this.cells[0] && this.cells[0].length) || 0;
    if ((axis === "row" && rows <= 1) || (axis === "col" && cols <= 1)) {
      new Notice("Better Tables: a table needs at least one row and column.");
      return;
    }
    if (axis === "row") {
      this.cells.splice(index, 1);
      this.rowH.splice(index, 1);
    } else {
      // In page-width mode, give the deleted column's width to its immediate
      // neighbours so non-adjacent columns keep their visual widths.
      if (this.pageWidth) {
        const deletedVal = this.colW[index];
        for (const row of this.cells) row.splice(index, 1);
        this.colW.splice(index, 1);
        this.colAlign.splice(index, 1);
        // Adjacent indices after splice: left = index-1, right = index
        const left = index - 1;
        const right = index;
        const adj = [];
        if (left >= 0) adj.push(left);
        if (right < this.colW.length) adj.push(right);
        if (adj.length > 0) {
          const adjTotal = adj.reduce((s, i) => s + this.colW[i], 0);
          let remaining = deletedVal;
          for (let a = 0; a < adj.length - 1; a++) {
            const share = Math.round(deletedVal * this.colW[adj[a]] / adjTotal);
            this.colW[adj[a]] += share;
            remaining -= share;
          }
          this.colW[adj[adj.length - 1]] += remaining; // absorbs rounding
        }
      } else {
        for (const row of this.cells) row.splice(index, 1);
        this.colW.splice(index, 1);
        this.colAlign.splice(index, 1);
      }
    }
    this.clearLineSelection();
    this.save();
  }

  /** Remove the entire ```table block (fences included) from the note. */
  tryEditorDelete(plugin, sourcePath, sec) {
    if (!sec || !plugin.app.workspace) return false;
    const allLeaves = [];
    plugin.app.workspace.iterateAllLeaves((l) => allLeaves.push(l));
    for (let li = 0; li < allLeaves.length; li++) {
      const leaf = allLeaves[li];
      const view = leaf.view;
      if (!view) continue;
      const file = view.file;
      if (!file || file.path !== sourcePath) continue;
      // --- CM6 / standard Obsidian editor path ---
      const editor = view.editor;
      if (editor && typeof editor.getLine === "function") {
        const open = editor.getLine(sec.lineStart);
        const close = editor.getLine(sec.lineEnd);
        const fenceOpen = /^\s*(`{3,}|~{3,})\s*table\b/.test(open || "");
        const fenceClose = /^\s*(`{3,}|~{3,})\s*$/.test(close || "");
        if (!fenceOpen || !fenceClose) return false;
        // Remove from the start of the opening fence through the end of the
        // closing fence, plus one trailing blank line if present.
        let endLine = sec.lineEnd;
        const nextLine = editor.getLine(endLine + 1);
        if (nextLine !== undefined && nextLine.trim() === "") endLine++;
        editor.replaceRange(
          "",
          { line: sec.lineStart, ch: 0 },
          { line: endLine + 1, ch: 0 }
        );
        return true;
      }
      // --- ProseMirror path ---
      const pm = view.pmView || (view.editor && (view.editor.pm || (view.editor.getDoc && view.editor.getDoc().pm)));
      if (pm && pm.state && pm.dispatch) {
        const doc = pm.state.doc;
        let found = false;
        doc.descendants((node, pos) => {
          if (found) return;
          if (node.type.name === "code_block" && node.attrs && node.attrs.language === "table") {
            // Delete from start of heading to end of code_block + one more line
            const from = pos;
            const to = pos + node.nodeSize;
            const tr = pm.state.tr;
            tr.delete(from, to);
            pm.dispatch(tr);
            found = true;
          }
        });
        if (found) return true;
      }
    }
    return false;
  }

  /** Remove the entire ```table block (fences included) from the note. */
  deleteTable() {
    const el = this.el;
    const ctx = this.ctx;
    const plugin = this.plugin;
    const oldBody = this.source;
    const info = ctx.getSectionInfo(el);
    const sec = info || ctx.getSectionInfo(el);

    // Use the editor API when possible so the deletion is undoable.
    if (sec && this.tryEditorDelete(plugin, ctx.sourcePath, sec)) {
      new Notice("Better Tables: table deleted.");
      return;
    }

    // Fallback: vault.process() deletion.
    plugin.queueWrite(async () => {
      const file = plugin.app.vault.getAbstractFileByPath(ctx.sourcePath);
      if (!file) return;
      const sec = info || ctx.getSectionInfo(el);
      try {
        await plugin.app.vault.process(file, (data) => {
          // 1) Precise path: drop the validated fenced line range, plus one
          //    trailing blank line if present, so we don't leave a gap.
          if (sec) {
            const lines = data.split("\n");
            const open = lines[sec.lineStart];
            const close = lines[sec.lineEnd];
            const fenceOpen = /^\s*(`{3,}|~{3,})\s*table\b/.test(open || "");
            const fenceClose = /^\s*(`{3,}|~{3,})\s*$/.test(close || "");
            if (fenceOpen && fenceClose) {
              let end = sec.lineEnd;
              if ((lines[end + 1] || "").trim() === "") end++;
              lines.splice(sec.lineStart, end - sec.lineStart + 1);
              return lines.join("\n");
            }
          }
          // 2) Fallback: find the body, expand to the surrounding fences, and cut
          //    the whole block — only if the body occurs exactly once.
          if (oldBody && oldBody.trim()) {
            const idx = data.indexOf(oldBody);
            if (idx !== -1 && data.indexOf(oldBody, idx + 1) === -1) {
              const before = data.slice(0, idx);
              const after = data.slice(idx + oldBody.length);
              const openMatch = before.match(/(?:^|\n)([ \t]*(?:`{3,}|~{3,})[ \t]*table\b[^\n]*\n)$/);
              const closeMatch = after.match(/^(\s*\n?[ \t]*(?:`{3,}|~{3,})[ \t]*)/);
              if (openMatch && closeMatch) {
                const start = idx - openMatch[1].length;
                let stop = idx + oldBody.length + closeMatch[1].length;
                if (data[stop] === "\n") stop++;
                return data.slice(0, start) + data.slice(stop);
              }
            }
          }
          return data; // couldn't locate the block safely — leave file untouched
        });
        new Notice("Better Tables: table deleted.");
      } catch (err) {
        console.error("Better Tables: delete failed", err);
        new Notice("Better Tables: failed to delete table.");
      }
    });
  }

  makeGhost(axis, index) {
    const t = this.tableEl;
    const g = this.rootEl.createDiv({ cls: "cp-table-ghost" });
    const gt = g.createEl("table", { cls: "cp-table" });
    if (axis === "row") {
      const src = t.rows[index];
      const tr = gt.createEl("tr");
      Array.from((src && src.cells) || []).forEach((cell) => {
        const td = tr.createEl("td");
        td.setText(cell.textContent || "");
        td.style.width = `${cell.offsetWidth}px`;
      });
      tr.style.height = `${(src && src.offsetHeight) || TABLE_CELL_H}px`;
      g.style.width = `${t.offsetWidth}px`;
    } else {
      Array.from(t.rows).forEach((row) => {
        const cell = row.cells[index];
        const tr = gt.createEl("tr");
        const td = tr.createEl("td");
        td.setText((cell && cell.textContent) || "");
        td.style.width = `${(cell && cell.offsetWidth) || TABLE_CELL_W}px`;
        tr.style.height = `${row.offsetHeight}px`;
      });
      g.style.width = `${(t.rows[0] && t.rows[0].cells[index] && t.rows[0].cells[index].offsetWidth) || TABLE_CELL_W}px`;
    }
    gt.style.width = "100%";
    return g;
  }

  // --- persistence: write the block back into the note file ---
  /** If the underlying content editor is a ProseMirror-based view, return
   *  keyboard focus to its DOM element so that key handlers (including Ctrl+Z
   *  / Ctrl+Shift+Z) work.  The table's own mousedown handler calls
   *  stopPropagation, which prevents the editor from claiming focus naturally —
   *  without this refocus the PM keymap never fires. */
  focusEditor() {
    if (!this.plugin || !this.plugin.app || !this.plugin.app.workspace) return;
    const leaf = this.plugin.app.workspace.activeLeaf;
    if (!leaf) return;
    const view = leaf.view;
    if (!view) return;
    const pm = view.pmView;
    if (pm && pm.dom && typeof pm.dom.focus === "function") {
      pm.dom.focus({ preventScroll: true });
    }
  }

  serialize() {
    const md = mdFromCells(this.cells, this.colAlign);
    const sizeLine = `<!-- tk:cols=${this.colW.join(",")};rows=${this.rowH.join(",")}${this.pageWidth ? ";fit=1" : ""} -->`;
    return `${md}\n${sizeLine}`;
  }

  /** Try to persist by replacing the fenced block via the editor API.
   *  Returns true on success, false when no matching editor is open (caller
   *  should fall back to vault.process).  Editor transactions go through CM6's
   *  undo stack or ProseMirror's history so Ctrl+Z / Ctrl+Shift+Z work on
   *  every table operation. */
  tryEditorSave(plugin, sourcePath, sec, body) {
    if (!sec || !plugin.app.workspace) return false;
    const leaves = plugin.app.workspace.getLeavesOfType("markdown");
    // Check all leaf types, not just "markdown"
    const allLeaves = [];
    plugin.app.workspace.iterateAllLeaves((l) => allLeaves.push(l));
    for (let li = 0; li < allLeaves.length; li++) {
      const leaf = allLeaves[li];
      const view = leaf.view;
      if (!view) continue;
      const file = view.file;
      if (!file || file.path !== sourcePath) continue;
      // --- CM6 / standard Obsidian editor path ---
      const editor = view.editor;
      if (editor && typeof editor.getLine === "function") {
        const open = editor.getLine(sec.lineStart);
        const close = editor.getLine(sec.lineEnd);
        const fenceOpen = /^\s*(`{3,}|~{3,})\s*table\b/.test(open || "");
        const fenceClose = /^\s*(`{3,}|~{3,})\s*$/.test(close || "");
        if (fenceOpen && fenceClose) {
          const newContent = open + "\n" + body + "\n" + close;
          editor.replaceRange(
            newContent,
            { line: sec.lineStart, ch: 0 },
            { line: sec.lineEnd, ch: close.length }
          );
          return true;
        }
      }
      // --- ProseMirror path ---
      const pm = view.pmView || (view.editor && (view.editor.pm || (view.editor.getDoc && view.editor.getDoc().pm)));
      if (pm && pm.state && pm.dispatch) {
        const doc = pm.state.doc;
        let found = false;
        doc.descendants((node, pos) => {
          if (found) return;
          if (node.type.name === "code_block" && node.attrs && node.attrs.language === "table") {
            const from = pos + 1;
            const to = pos + node.nodeSize - 1;
            const tr = pm.state.tr;
            tr.replaceWith(from, to, pm.state.schema.text(body));
            pm.dispatch(tr);
            found = true;
          }
        });
        if (found) return true;
      }
    }
    return false;
  }

  save() {
    // Capture horizontal scroll position so we can restore it after the
    // re-render that vault.process / editor transaction will trigger.
    // Otherwise the table always jumps back to column 0 after every edit.
    const scrollEl = this.el.querySelector(".cp-table-scroll");
    if (scrollEl) this.plugin._btPendingScroll = scrollEl.scrollLeft;

    this.dirty = false;
    const oldBody = this.source;
    const body = this.serialize();
    this.source = body;
    const el = this.el;
    const ctx = this.ctx;
    const plugin = this.plugin;
    // Capture the block's line range NOW, while the element is still attached.
    // It can be null right after a block is created (Obsidian hasn't indexed it
    // yet) — in that case we fall back to locating the block by its content.
    const info = ctx.getSectionInfo(el);
    const sec = info || ctx.getSectionInfo(el);

    // Use the editor API when possible so changes flow through CM6's undo
    // stack and Ctrl+Z / Ctrl+Shift+Z work on every table operation.
    if (sec && this.tryEditorSave(plugin, ctx.sourcePath, sec, body)) return;

    // Fallback: persist through the vault API.  This path is taken when no
    // markdown editor is available for the file (reading view, file closed).
    plugin.queueWrite(async () => {
      const file = plugin.app.vault.getAbstractFileByPath(ctx.sourcePath);
      if (!file) return;
      try {
        await plugin.app.vault.process(file, (data) => {
          // 1) Precise path: replace a validated fenced line range.
          if (sec) {
            const lines = data.split("\n");
            const open = lines[sec.lineStart];
            const close = lines[sec.lineEnd];
            const fenceOpen = /^\s*(`{3,}|~{3,})\s*table\b/.test(open || "");
            const fenceClose = /^\s*(`{3,}|~{3,})\s*$/.test(close || "");
            if (fenceOpen && fenceClose) {
              const newLines = [open, ...body.split("\n"), close];
              lines.splice(sec.lineStart, sec.lineEnd - sec.lineStart + 1, ...newLines);
              return lines.join("\n");
            }
          }
          // 2) Fallback: replace the previous block body by content, but only
          //    if it occurs exactly once (otherwise we can't be sure which).
          if (oldBody && oldBody.trim()) {
            const idx = data.indexOf(oldBody);
            if (idx !== -1 && data.indexOf(oldBody, idx + 1) === -1) {
              return data.slice(0, idx) + body + data.slice(idx + oldBody.length);
            }
          }
          return data; // couldn't locate the block safely — leave file untouched
        });
      } catch (err) {
        console.error("Better Tables: save failed", err);
        new Notice("Better Tables: failed to save table.");
      }
    });
  }
}

module.exports = class BetterTablesPlugin extends Plugin {
  async onload() {
    // Serializes all table writes so concurrent saves can never interleave.
    this._writeChain = Promise.resolve();

    this.settings = Object.assign({}, DEFAULT_SETTINGS, await this.loadData());
    this.addSettingTab(new BetterTablesSettingTab(this.app, this));

    this.registerMarkdownCodeBlockProcessor("table", (source, el, ctx) => {
      const widget = new TableWidget(this, source, el, ctx);
      // Tie the widget's lifetime to the block: when Obsidian unloads this
      // section (re-render, pane close, plugin unload) the child unloads and we
      // release the ResizeObserver, link-suggest listeners, and markdown host.
      const child = new MarkdownRenderChild(el);
      child.register(() => widget.destroy());
      ctx.addChild(child);
      widget.render();
    });

    // When a table cell is being edited, Obsidian shows its native editor menu.
    // The cell's contextmenu handler flags which column was clicked; here we
    // append our Align items so they live alongside Cut/Copy/Paste.
    this.registerEvent(
      this.app.workspace.on("editor-menu", (menu) => {
        const p = this.pendingAlign;
        this.pendingAlign = null;
        if (!p || Date.now() - p.at > 1000) return;
        menu.addSeparator();
        p.widget.addAlignItems(menu, p.col);
      })
    );

    this.addCommand({
      id: "insert-table",
      name: "Insert table",
      editorCallback: (editor) => {
        const block = ["```table", "|     |     |", "| --- | --- |", "|     |     |", "```", ""].join("\n");
        editor.replaceSelection(block);
      }
    });
  }

  async saveSettings() {
    await this.saveData(this.settings);
  }

  /** Run write tasks one at a time, in order. */
  queueWrite(task) {
    this._writeChain = this._writeChain.then(task, task);
    return this._writeChain;
  }
};

class BetterTablesSettingTab extends PluginSettingTab {
  constructor(app, plugin) {
    super(app, plugin);
    this.plugin = plugin;
  }

  display() {
    const { containerEl } = this;
    containerEl.empty();
    new Setting(containerEl)
      .setName("Quick text edit")
      .setDesc(
        "On: a single click on a cell edits its text immediately. " +
          "Off: the first click selects the cell and a second click (or Enter) starts editing."
      )
      .addToggle((toggle) =>
        toggle.setValue(this.plugin.settings.quickEdit).onChange(async (value) => {
          this.plugin.settings.quickEdit = value;
          await this.plugin.saveSettings();
        })
      );
  }
}

/* nosourcemap */
/* nosourcemap */
