import {
    workspace,
    ExtensionContext,
    window,
} from "vscode";

import {
    Disposable,
    Executable,
    LanguageClient,
    LanguageClientOptions,
    ServerOptions,
} from "vscode-languageclient/node";

let client: LanguageClient;

export async function activate(context: ExtensionContext) {
    const traceOutputChannel = window.createOutputChannel("MFL Language Server trace");
    const command = "mfl-lsp-server";
    const run: Executable = {
        command,
        options: {
            env: {
                ...process.env,
                RUST_LOG: "debug",
            }
        }
    };
    const serverOptions: ServerOptions = {
        run,
        debug: run,
    };

    // If the extension is launched in debug mode then the debug server options are used.
    // Otherwise the run options are used.
    let clientOptions: LanguageClientOptions = {
        documentSelector: [{ scheme: "file", language: "mfl" }],
        synchronize: {},
        traceOutputChannel,
    };

    // Create the language client and start the client.
    client = new LanguageClient("mfl-language-server", "MFL Language Server", serverOptions, clientOptions);
    client.start();
}

export function deactivate(): Thenable<void> | undefined {
    if (!client) {
        return undefined;
    }
    return client.stop();
}