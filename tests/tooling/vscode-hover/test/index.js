const vscode = require('vscode');
const fs = require('fs');
const path = require('path');
const OUT = '/tmp/claude-1000/-home-schorsch/d0785ee2-006f-4d83-9fb1-30d6cfb3c6d2/scratchpad/hover-out.json';

exports.run = async function run() {
  const results = { hovers: [], errors: [] };
  try {
    const folders = vscode.workspace.workspaceFolders || [];
    results.workspace = folders.map(f => f.uri.fsPath);
    const file = path.join(folders[0].uri.fsPath, 'main.fpp');
    const doc = await vscode.workspace.openTextDocument(file);
    await vscode.window.showTextDocument(doc);
    const ext = vscode.extensions.getExtension('fpp.fpp');
    results.extension = ext ? ('found, active=' + ext.isActive) : 'NOT FOUND';
    if (ext && !ext.isActive) { await ext.activate(); results.extension += ' -> activated'; }

    const lines = doc.getText().split('\n');
    const findLine = needle => lines.findIndex(l => l.includes(needle));
    const dl = findLine('let double x = x + x');
    for (let i = 0; i < 90; i++) {
      const probe = await vscode.commands.executeCommand('vscode.executeHoverProvider', doc.uri, new vscode.Position(dl, 4));
      if (probe && probe.length) { results.readyAfterSeconds = i; break; }
      await new Promise(r => setTimeout(r, 1000));
    }
    const intUse = findLine('double 21');
    const strUse = findLine('double \\"ab\\"');
    const probes = [
      ['double (generic definition)', dl, 4],
      ['x (its parameter)', dl, 11],
      // the CALL, not the same word inside the format string
      ['double at the int use', intUse, lines[intUse] ? lines[intUse].lastIndexOf('double') + 2 : 0],
      ['double at the string use', strUse, lines[strUse] ? lines[strUse].lastIndexOf('double') + 2 : 0],
      ['ints (a binding)', findLine('let ints'), 4],
    ];
    for (const [what, line, ch] of probes) {
      if (line < 0) { results.hovers.push({ what, hover: '(line not found)' }); continue; }
      const hs = await vscode.commands.executeCommand('vscode.executeHoverProvider', doc.uri, new vscode.Position(line, ch));
      const rendered = (hs || []).map(h => h.contents.map(c => (typeof c === 'string' ? c : c.value)).join(' ')).join(' | ');
      results.hovers.push({ what, line: line + 1, sourceLine: lines[line].trim(), hover: rendered.replace(/```fpp|```/g, '').trim() });
    }
  } catch (e) {
    results.errors.push(String((e && e.stack) || e));
  }
  fs.writeFileSync(OUT, JSON.stringify(results, null, 2));
};
