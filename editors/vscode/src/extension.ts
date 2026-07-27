import * as fs from 'fs';
import * as path from 'path';
import * as vscode from 'vscode';
import {
    LanguageClient,
    LanguageClientOptions,
    ServerOptions,
    TransportKind,
} from 'vscode-languageclient/node';

let client: LanguageClient | undefined;

/// The server is a .NET stdio program. Either a published binary, or — the
/// normal case while working on the compiler itself — `dotnet run` against
/// the LSP project, so an edit to the compiler is one rebuild away from
/// being live in the editor.
function serverOptions(folder: vscode.WorkspaceFolder | undefined): ServerOptions {
    const config = vscode.workspace.getConfiguration('fpp');
    const explicit = (config.get<string>('server.path') ?? '').trim();
    if (explicit.length > 0) {
        return { command: explicit, transport: TransportKind.stdio };
    }
    const rel = config.get<string>('server.project') ?? 'src/Fpp.Lsp/Fpp.Lsp.fsproj';
    const root = folder?.uri.fsPath ?? process.cwd();
    const project = path.isAbsolute(rel) ? rel : path.join(root, rel);
    return {
        command: 'dotnet',
        // --no-build would be faster but silently serves a stale server after
        // a compiler change, which is exactly the confusing case to avoid
        args: ['run', '--project', project, '-c', 'Release', '--'],
        transport: TransportKind.stdio,
        options: { cwd: root },
    };
}

export async function activate(context: vscode.ExtensionContext) {
    const folder = vscode.workspace.workspaceFolders?.[0];

    const clientOptions: LanguageClientOptions = {
        documentSelector: [{ scheme: 'file', language: 'fpp' }],
        synchronize: {
            // the manifest fixes the compile order, so a change to it
            // invalidates everything the server believes
            fileEvents: vscode.workspace.createFileSystemWatcher('**/*.fppproj'),
        },
        outputChannelName: 'F++',
    };

    client = new LanguageClient('fpp', 'F++ Language Server', serverOptions(folder), clientOptions);
    await client.start();
    context.subscriptions.push({ dispose: () => { void client?.stop(); } });

    context.subscriptions.push(
        vscode.commands.registerCommand('fpp.restartServer', async () => {
            await client?.restart();
        }),
        vscode.commands.registerCommand('fpp.build', () => buildProject(folder)),
    );
}

/// `fpp build` on the nearest manifest, as a VS Code task so its output and
/// exit code land in the terminal rather than being swallowed.
async function buildProject(folder: vscode.WorkspaceFolder | undefined) {
    if (!folder) {
        void vscode.window.showErrorMessage('F++: no workspace folder is open');
        return;
    }
    const found = await vscode.workspace.findFiles('**/*.fppproj', '**/node_modules/**', 2);
    if (found.length === 0) {
        void vscode.window.showErrorMessage('F++: no .fppproj found in this workspace');
        return;
    }
    const proj = found[0].fsPath;
    const cliProject = path.join(folder.uri.fsPath, 'src', 'Fpp.Cli', 'Fpp.Cli.fsproj');
    const command = fs.existsSync(cliProject)
        ? `dotnet run --project ${quote(cliProject)} -c Release -- build ${quote(proj)}`
        : `fpp build ${quote(proj)}`;
    const task = new vscode.Task(
        { type: 'shell' },
        folder,
        'fpp build',
        'fpp',
        new vscode.ShellExecution(command, { cwd: folder.uri.fsPath }),
    );
    await vscode.tasks.executeTask(task);
}

function quote(p: string): string {
    return /[\s"']/.test(p) ? `"${p.replace(/"/g, '\\"')}"` : p;
}

export function deactivate(): Thenable<void> | undefined {
    return client?.stop();
}
