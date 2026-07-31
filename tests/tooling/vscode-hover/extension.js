const fsBoot = require('fs');
fsBoot.appendFileSync('/tmp/claude-1000/-home-schorsch/d0785ee2-006f-4d83-9fb1-30d6cfb3c6d2/scratchpad/driver-boot.log', 'module loaded ' + new Date().toISOString() + '\n');
const vscode = require('vscode');
const fs = require('fs');
const path = require('path');
const OUT = '/tmp/claude-1000/-home-schorsch/d0785ee2-006f-4d83-9fb1-30d6cfb3c6d2/scratchpad/hover-out.json';

async function activate(context) {
  fsBoot.appendFileSync('/tmp/claude-1000/-home-schorsch/d0785ee2-006f-4d83-9fb1-30d6cfb3c6d2/scratchpad/driver-boot.log', 'activate ' + new Date().toISOString() + '\n');
  const results = { started: new Date().toISOString(), hovers: [], errors: [] };
  try {
    const folders = vscode.workspace.workspaceFolders || [];
    results.workspace = folders.map(f => f.uri.fsPath);
    const file = path.join(folders[0].uri.fsPath, 'main.fpp');
    const doc = await vscode.workspace.openTextDocument(file);
    await vscode.window.showTextDocument(doc);
    results.extensions = vscode.extensions.all.filter(e => e.id.toLowerCase().includes('fpp')).map(e => e.id + ' active=' + e.isActive);

    // give the language server time to start and check the project
    const log = m => fsBoot.appendFileSync('/tmp/claude-1000/-home-schorsch/d0785ee2-006f-4d83-9fb1-30d6cfb3c6d2/scratchpad/driver-boot.log', m + '\n');
    log('opened doc, extensions: ' + results.extensions.join(','));
    for (let i = 0; i < 45; i++) {
      const probe = await vscode.commands.executeCommand('vscode.executeHoverProvider', doc.uri, new vscode.Position(7, 4));
      if (probe && probe.length) { log('hover available after ' + i + 's'); break; }
      await new Promise(r => setTimeout(r, 1000));
    }

    // hover the things a person would: a generic function, a call, a parameter
    const text = doc.getText();
    const lines = text.split('\n');
    const want = [
      ['double (definition)', 7, 4],
      ['double (use)', 9, 44],
      ['x (parameter)', 7, 11],
    ];
    for (const [what, line, ch] of want) {
      const hs = await vscode.commands.executeCommand('vscode.executeHoverProvider', doc.uri, new vscode.Position(line, ch));
      const rendered = (hs || []).map(h => h.contents.map(c => (typeof c === 'string' ? c : c.value)).join(' ')).join(' | ');
      results.hovers.push({ what, line: line + 1, sourceLine: (lines[line] || '').trim(), hover: rendered.trim() });
    }
  } catch (e) {
    results.errors.push(String(e && e.stack || e));
  }
  fs.writeFileSync(OUT, JSON.stringify(results, null, 2));
  // let the harness see we finished, then close the editor
  setTimeout(() => vscode.commands.executeCommand('workbench.action.quit'), 500);
}
exports.activate = activate;
