"use strict";

const scopeRoot = document.getElementById("scope-root");
const reportRoot = document.getElementById("eval-live-root");
const encodedEnvelope = document.getElementById("report-envelope").textContent.trim();
const envelope = JSON.parse(new TextDecoder().decode(bytesFromBase64(encodedEnvelope)));
let currentPayload = envelope.initial_payload;
let applyScope = null;

function bytesFromBase64(value) {
  const binary = atob(value);
  const bytes = new Uint8Array(binary.length);
  for (let index = 0; index < binary.length; index += 1) bytes[index] = binary.charCodeAt(index);
  return bytes;
}

function element(tag, text, className) {
  const node = document.createElement(tag);
  if (text !== undefined && text !== null) node.textContent = text;
  if (className) node.className = className;
  return node;
}

function endpointField(labelText, id, endpoints, selectedId, ready) {
  const label = element("label", labelText + " ");
  const select = element("select");
  select.id = id;
  select.disabled = !ready;
  for (const endpoint of endpoints) {
    const option = element("option", endpoint.label);
    option.value = endpoint.id;
    option.selected = endpoint.id === selectedId;
    select.appendChild(option);
  }
  label.appendChild(select);
  return label;
}

function renderScope(selectors, reportPath, statusText, ready) {
  scopeRoot.replaceChildren();
  const heading = element("h1", "Benchmark report");
  const note = element(
    "p",
    `Snapshot: ${reportPath}. Selectors only recompute cached observations; they never run a benchmark.`,
    "scope-note",
  );
  const form = element("form", null, "scope-form");

  const pair = element("fieldset", null, "scope-pair");
  pair.appendChild(element("legend", "Comparison"));
  pair.append(
    endpointField("Baseline", "scope-baseline", selectors.endpoints, selectors.baseline_endpoint_id, ready),
    endpointField("Candidate", "scope-candidate", selectors.endpoints, selectors.candidate_endpoint_id, ready),
  );
  const swap = element("button", "Swap endpoints");
  swap.type = "button";
  swap.disabled = !ready;
  swap.addEventListener("click", () => {
    const baseline = document.getElementById("scope-baseline");
    const candidate = document.getElementById("scope-candidate");
    [baseline.value, candidate.value] = [candidate.value, baseline.value];
  });
  pair.appendChild(swap);

  const files = element("fieldset");
  files.appendChild(element("legend", "Files"));
  for (const file of selectors.files) {
    const label = element("label", null, "scope-choice");
    const input = element("input");
    input.type = "checkbox";
    input.dataset.kind = "file";
    input.value = file.id;
    input.checked = file.selected;
    input.disabled = !ready;
    label.append(input, document.createTextNode(" " + file.label));
    files.appendChild(label);
  }

  const sampling = element("fieldset");
  sampling.appendChild(element("legend", "Sampling"));
  const timeoutLabel = element("label", "Timeout ");
  const timeout = element("select");
  timeout.id = "scope-timeout";
  timeout.disabled = !ready;
  for (const value of selectors.timeouts_sec) {
    const option = element("option", `${value} s`);
    option.value = String(value);
    option.selected = value === selectors.timeout_sec;
    timeout.appendChild(option);
  }
  timeoutLabel.appendChild(timeout);
  const roundsLabel = element("label", "Rounds ");
  const rounds = element("input");
  rounds.id = "scope-rounds";
  rounds.type = "number";
  rounds.min = "1";
  rounds.max = String(selectors.max_rounds);
  rounds.step = "1";
  rounds.value = String(selectors.rounds);
  rounds.disabled = !ready;
  roundsLabel.appendChild(rounds);
  sampling.append(timeoutLabel, roundsLabel);

  form.append(pair, files, sampling);
  const actions = element("div", null, "scope-actions");
  const apply = element("button", "Apply");
  apply.type = "submit";
  apply.disabled = !ready;
  const status = element("span", statusText, "scope-status");
  status.setAttribute("role", "status");
  status.setAttribute("aria-live", "polite");
  actions.append(apply, status);
  form.appendChild(actions);
  form.addEventListener("submit", async (event) => {
    event.preventDefault();
    if (!applyScope) return;
    const request = {
      baseline_endpoint_id: document.getElementById("scope-baseline").value,
      candidate_endpoint_id: document.getElementById("scope-candidate").value,
      file_ids: [...scopeRoot.querySelectorAll('input[data-kind="file"]:checked')].map((input) => input.value),
      timeout_sec: Number(document.getElementById("scope-timeout").value),
      rounds: Number(document.getElementById("scope-rounds").value),
    };
    renderScope(currentPayload.selectors, currentPayload.report_path, "Recomputing cached report...", false);
    try {
      const result = JSON.parse(await applyScope(JSON.stringify(request)));
      if (!result.ok) throw new Error(result.error);
      renderPayload(result.payload, "Ready", true);
    } catch (error) {
      renderScope(currentPayload.selectors, currentPayload.report_path, `Cannot apply selection: ${error}`, true);
    }
  });
  scopeRoot.append(heading, note, form);
}

function renderPayload(payload, statusText, ready) {
  currentPayload = payload;
  renderScope(payload.selectors, payload.report_path, statusText, ready);
  initEvalLiveCatalog(reportRoot, payload.sections);
}

function loadScript(src) {
  return new Promise((resolve, reject) => {
    const script = document.createElement("script");
    script.src = src;
    script.addEventListener("load", resolve, {once: true});
    script.addEventListener("error", () => reject(new Error(`failed to load ${src}`)), {once: true});
    document.head.appendChild(script);
  });
}

async function initializeRuntime() {
  renderScope(currentPayload.selectors, currentPayload.report_path, "Loading Python runtime...", false);
  await loadScript(envelope.pyodide_base_url + "pyodide.js");
  const pyodide = await loadPyodide({indexURL: envelope.pyodide_base_url});
  renderScope(currentPayload.selectors, currentPayload.report_path, "Loading SciPy...", false);
  await pyodide.loadPackage("scipy");

  for (const [filename, source] of Object.entries(envelope.python_modules)) {
    const path = "/home/pyodide/" + filename;
    pyodide.FS.mkdirTree(path.slice(0, path.lastIndexOf("/")));
    pyodide.FS.writeFile(path, source, {encoding: "utf8"});
  }
  const virtualReportPath = "/home/pyodide/benchmark-report.jsonl";
  pyodide.FS.writeFile(virtualReportPath, bytesFromBase64(envelope.report_jsonl_base64));
  pyodide.globals.set("_egglog_report_path", virtualReportPath);
  pyodide.globals.set("_egglog_report_display_path", envelope.report_path);
  pyodide.globals.set("_egglog_initial_scope_json", JSON.stringify(envelope.initial_scope));
  await pyodide.runPythonAsync(envelope.python_bootstrap);
  applyScope = pyodide.globals.get("_egglog_apply_scope");
  renderScope(currentPayload.selectors, currentPayload.report_path, "Ready", true);
}

renderPayload(currentPayload, "Loading Python runtime...", false);
initializeRuntime().catch((error) => {
  renderScope(
    currentPayload.selectors,
    currentPayload.report_path,
    `Interactive analysis unavailable; the embedded report is still complete. ${error}`,
    false,
  );
});
