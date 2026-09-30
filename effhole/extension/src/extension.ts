// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import * as vscode from 'vscode';
import * as fs from 'fs';

class MyInlayHintsProvider implements vscode.InlayHintsProvider {
	// 核心方法：返回提示数组
	async provideInlayHints(
		document: vscode.TextDocument,
		range: vscode.Range,
		token: vscode.CancellationToken
	): Promise<vscode.InlayHint[]> {
		const fileContent = document.getText();

		let res: any;
		try {
			res = await sendRequest('getHoleID', fileContent, { showHealthGuide: false });
		} catch (error: any) {
			console.warn(`EffHole inlay request failed: ${error.message}`);
			return [];
		}

		if (!res || res["status"] !== 0) {
			return [];
		}
		else {
			// res should have "holeMap"
			let list = res["holeMap"].map((item: any) => {
				return new vscode.InlayHint(
					new vscode.Position(item[0][0] - 1, item[0][1]), // vscode uses 0-based indexing
					item[1],
					vscode.InlayHintKind.Parameter 
				);
			});
			return list;
		}
	}
}

let panel: vscode.WebviewPanel | undefined = undefined;
let currentEvalResult: string | undefined = undefined;
let currentHoleContext: Record<string, HoleContextMap> = {};
let currentHoleContextQueue: HoleContextQueueEntry[] = [];
let currentSteps: any[] = [];
let currentStepIndex = 0;
let stepModeEnabled = false;
let currentFocusedRange: any = undefined;
let currentFocusText: string | undefined = undefined;
let currentRunStatus = 0;
let currentRunErrorMessage: string | undefined = undefined;
let currentFinalResult: string | undefined = undefined;
let currentFinalHoleContext: Record<string, HoleContextMap> = {};
let extensionContext: vscode.ExtensionContext;
let currentSourceDocumentUri: vscode.Uri | undefined = undefined;
let holeDefinitionDecorationType: vscode.TextEditorDecorationType | undefined = undefined;
let currentHoleDefinitions: HoleDefinitionMap = {};
let hoveredHoleDefinition: DefinitionRange | undefined = undefined;
let hoveredContextDefinition: DefinitionRange | undefined = undefined;
let lastHealthCheckedAt = 0;
let lastHealthOk = false;
let lastHealthErrorShownAt = 0;
let currentRunMode: BaseMode = 'eval';

type BaseMode = 'eval' | 'norm';
type ServerCommand = 'eval' | 'norm' | 'evalStep' | 'normStep' | 'getHoleID' | 'logHoleClick';
type RequestPayload = {
	command: ServerCommand;
	content: string;
	fuel?: number;
	username: string;
	timestamp: number;
	holeName?: string;
	holeContext?: HoleContextMap;
};

type SendRequestOptions = {
	showHealthGuide?: boolean;
};

type CodePosition = {
	line: number;
	column: number;
};

type DefinitionRange = {
	start: CodePosition;
	end: CodePosition;
};

type HoleContextEntry = {
	value: string;
	definition?: DefinitionRange;
};

type HoleContextMap = Record<string, HoleContextEntry>;

type HoleContextQueueEntry = {
	holeName: string;
	context: HoleContextMap;
};

type HoleDefinitionMap = Record<string, DefinitionRange>;

// This method is called when your extension is activated
// Your extension is activated the very first time the command is executed
export function activate(context: vscode.ExtensionContext) {
	extensionContext = context;
	const storedMode = context.globalState.get<string>('runMode');
	setCurrentRunMode(isBaseMode(storedMode) ? storedMode : 'eval');
	if (!holeDefinitionDecorationType) {
		holeDefinitionDecorationType = vscode.window.createTextEditorDecorationType({
			backgroundColor: new vscode.ThemeColor('editor.findMatchHighlightBackground'),
			border: '1px solid',
			borderColor: new vscode.ThemeColor('editorWarning.foreground'),
			borderRadius: '2px',
			overviewRulerColor: new vscode.ThemeColor('editorWarning.foreground'),
			overviewRulerLane: vscode.OverviewRulerLane.Right,
		});
		context.subscriptions.push(holeDefinitionDecorationType);
	}
	// Use the console to output diagnostic information (console.log) and errors (console.error)
	// This line of code will only be executed once when your extension is activated
	console.log('Congratulations, your extension "effhole" is now active!');

	// The command has been defined in the package.json file
	// Now provide the implementation of the command with registerCommand
	// The commandId parameter must match the command field in package.json
	/*
	const disposable = vscode.commands.registerCommand('effhole.helloWorld', () => {
		// The code you place here will be executed every time your command is executed
		// Display a message box to the user
		vscode.window.showInformationMessage('Hello World from EffHole!');
	});
	*/

	const runHandler = async () => {
			const editor = vscode.window.activeTextEditor;
			if (!editor) {
				vscode.window.showErrorMessage('No active editor');
				return;
			}

			if (editor.document.isDirty) {
				await editor.document.save();
			}

			currentSourceDocumentUri = editor.document.uri;
			clearHoleContextHighlight();
			const fileContent = editor.document.getText();
			await refreshHoleDefinitions(fileContent);
			const step = vscode.workspace.getConfiguration('effhole').get<boolean>('step') || false;
			await runEffHoleWithContent(currentRunMode, fileContent, undefined, step);
		};
    
    const normalizeHandler = async (text?: string) => {
        let content = text;
        // If text is not provided, try to get selection from active editor
        if (!content) {
            const editor = vscode.window.activeTextEditor;
            if (editor) {
                content = editor.document.getText(editor.selection);
            }
        }

        if (content) {
			// normalizeSelection should always return the final normalized result, not step views.
			await runEffHoleWithContent('norm', content, (res) => {
                if (res["status"] !== 0) {
                    vscode.window.showErrorMessage(`Normalization failed: ${res["error"]}`);
                } else {
                    vscode.window.showInformationMessage(`Normalization result: ${res["result"]}`);
                }
			}, false);
        } else {
            vscode.window.showInformationMessage('No text selected to normalize');
        }
    };

	context.subscriptions.push(vscode.commands.registerCommand('effhole.run', runHandler));
	context.subscriptions.push(vscode.commands.registerCommand('effhole.runWithKeys', runHandler));
	context.subscriptions.push(vscode.commands.registerCommand('effhole.normalizeSelection', normalizeHandler));
	const toggleRunModeHandler = () => {
		const nextMode: BaseMode = currentRunMode === 'eval' ? 'norm' : 'eval';
		setCurrentRunMode(nextMode);
	};
	context.subscriptions.push(vscode.commands.registerCommand('effhole.toggleRunModeEvalTitle', toggleRunModeHandler));
	context.subscriptions.push(vscode.commands.registerCommand('effhole.toggleRunModeNormTitle', toggleRunModeHandler));
	context.subscriptions.push(
        vscode.languages.registerInlayHintsProvider(
            { language: 'effhole' }, 
            new MyInlayHintsProvider()
        )
    );
}

function isBaseMode(value: unknown): value is BaseMode {
	return value === 'eval' || value === 'norm';
}

function setCurrentRunMode(mode: BaseMode): void {
	currentRunMode = mode;
	void vscode.commands.executeCommand('setContext', 'effhole.runMode', mode);
	void extensionContext.globalState.update('runMode', mode);
}

function getBackendBaseUrl(): string {
	const config = vscode.workspace.getConfiguration('effhole');
	const configuredUrl = config.get<unknown>('serverUrl');
	const raw = (typeof configuredUrl === 'string' ? configuredUrl : 'http://127.0.0.1:8081').trim();
	return raw.replace(/\/+$/, '');
}

function getRequestTimeoutMs(): number {
	const config = vscode.workspace.getConfiguration('effhole');
	const raw = config.get<number>('requestTimeoutMs');
	const timeout = Number.isFinite(raw) ? Math.floor(raw as number) : 10000;
	return timeout > 0 ? timeout : 10000;
}

function getHoleContextWindowSize(): number {
	const config = vscode.workspace.getConfiguration('effhole');
	const raw = config.get<number>('holeContextWindowSize');
	const size = Number.isFinite(raw) ? Math.floor(raw as number) : 5;
	return Math.min(Math.max(size, 1), 50);
}

async function requestBackend(payload: RequestPayload): Promise<any> {
	const controller = new AbortController();
	const timeoutId = setTimeout(() => controller.abort(), getRequestTimeoutMs());
	try {
		const response = await fetch(`${getBackendBaseUrl()}/api/v1/run`, {
			method: 'POST',
			headers: { 'Content-Type': 'application/json' },
			body: JSON.stringify(payload),
			signal: controller.signal,
		});

		const text = await response.text();
		const res = parseResult(text);
		if (!res) {
			throw new Error('Invalid JSON response from backend');
		}
		return res;
	} catch (error: any) {
		if (error?.name === 'AbortError') {
			throw new Error(`Request timeout after ${getRequestTimeoutMs()}ms`);
		}
		throw error;
	} finally {
		clearTimeout(timeoutId);
	}
}

function formatBackendGuideMessage(): string {
	const serverUrl = getBackendBaseUrl();
	return `Cannot reach EffHole backend at ${serverUrl}. Start backend first: stack run -- http --port 8081`;
}

async function showBackendGuideMessage(): Promise<void> {
	const now = Date.now();
	if (now - lastHealthErrorShownAt < 5000) {
		return;
	}
	lastHealthErrorShownAt = now;
	const action = await vscode.window.showErrorMessage(
		formatBackendGuideMessage(),
		'Open EffHole Settings'
	);
	if (action === 'Open EffHole Settings') {
		await vscode.commands.executeCommand('workbench.action.openSettings', 'effhole.serverUrl');
	}
}

async function checkBackendHealth(showGuide: boolean): Promise<boolean> {
	const now = Date.now();
	if (now - lastHealthCheckedAt < 3000) {
		if (!lastHealthOk && showGuide) {
			await showBackendGuideMessage();
		}
		return lastHealthOk;
	}

	const controller = new AbortController();
	const timeoutId = setTimeout(() => controller.abort(), Math.min(3000, getRequestTimeoutMs()));
	try {
		const response = await fetch(`${getBackendBaseUrl()}/health`, {
			method: 'GET',
			signal: controller.signal,
		});
		lastHealthCheckedAt = Date.now();
		lastHealthOk = response.ok;
		if (!lastHealthOk && showGuide) {
			await showBackendGuideMessage();
		}
		return lastHealthOk;
	} catch {
		lastHealthCheckedAt = Date.now();
		lastHealthOk = false;
		if (showGuide) {
			await showBackendGuideMessage();
		}
		return false;
	} finally {
		clearTimeout(timeoutId);
	}
}

async function sendRequest(command: ServerCommand, content: string, options?: SendRequestOptions): Promise<any | undefined> {
	const showHealthGuide = options?.showHealthGuide ?? false;
	const healthy = await checkBackendHealth(showHealthGuide);
	if (!healthy) {
		return undefined;
	}
	return requestBackend(buildRequestPayload(command, content));
}

async function runEffHole(filePath: string): Promise<void> {
	// read file to fileContent
	let fileContent = '';
	try {
		fileContent = fs.readFileSync(filePath, 'utf-8');
	} catch (err) {
		vscode.window.showInformationMessage(`Failed to read file: ${err}`);
		return;
	}
	const config = vscode.workspace.getConfiguration('effhole');
	const step = config.get<boolean>('step') || false;
	await runEffHoleWithContent(currentRunMode, fileContent, undefined, step);
}

function resolveServerCommand(baseMode: BaseMode, step: boolean): ServerCommand {
	if (!step) {
		return baseMode;
	}
	return baseMode === 'norm' ? 'normStep' : 'evalStep';
}

function getConfiguredFuel(): number {
	const config = vscode.workspace.getConfiguration('effhole');
	const rawFuel = config.get<number>('fuel');
	const fuel = Number.isFinite(rawFuel) ? Math.floor(rawFuel as number) : 1000;
	if (fuel <= 0) {
		return 1000;
	}
	return Math.min(fuel, 2000);
}

function getConfiguredUserName(): string {
	const config = vscode.workspace.getConfiguration('effhole');
	const rawUserName = config.get<string>('userName');
	const userName = typeof rawUserName === 'string' ? rawUserName.trim() : '';
	return userName || 'guest';
}

function buildRequestPayload(command: ServerCommand, content: string): RequestPayload {
	const payload: RequestPayload = {
		command,
		content,
		username: getConfiguredUserName(),
		timestamp: Date.now(),
	};
	if (command !== 'getHoleID') {
		payload.fuel = getConfiguredFuel();
	}
	return payload;
}

async function logHoleClick(holeName: string, holeContext: HoleContextMap): Promise<void> {
	try {
		await requestBackend({
			...buildRequestPayload('logHoleClick', ''),
			holeName,
			holeContext,
		});
	} catch (error: any) {
		console.warn(`EffHole hole click log failed: ${error.message}`);
	}
}

async function runEffHoleWithContent(baseMode: BaseMode, content: string, processResult?: (res: any) => void, step?: boolean): Promise<void> {
	const shouldStep = step ?? (vscode.workspace.getConfiguration('effhole').get<boolean>('step') || false);
	const command = resolveServerCommand(baseMode, shouldStep);
	try {
		const res = await sendRequest(command, content, { showHealthGuide: true });
		if (!res) {
			return;
		}
		if (processResult) {
			processResult(res);
		} else {
			showPanel(res);
		}
	} catch (error: any) {
		vscode.window.showErrorMessage(`EffHole request failed: ${error.message}`);
	}
}

function parseResult(result: string) {
	let res;
	try {
		res = JSON.parse(result);
	} catch (err) {
		vscode.window.showInformationMessage(`JSON parse failed: ${err}`);
		return;
	}

	return res;
}

function showPanel(result: any) {
	const hasSteps = Array.isArray(result["steps"]) && result["steps"].length > 0;
	currentRunStatus = typeof result["status"] === 'number' ? result["status"] : -1;
	currentRunErrorMessage = typeof result["error"] === 'string' ? result["error"] : undefined;

	if (hasSteps) {
		stepModeEnabled = true;
		currentSteps = result["steps"];
		currentStepIndex = 0;
		const lastStep = currentSteps[currentSteps.length - 1];
		const lastAfter = lastStep?.["after"] || {};
		currentFinalResult = result["result"] ?? lastAfter["result"] ?? '';
		currentFinalHoleContext = result["substMap"] ?? lastAfter["substMap"] ?? {};
		updateStateFromStepView(currentStepIndex);
	} else {
		if (result["status"] !== 0) {
			const html = getErrorWebviewContent(result["status"], result["error"]);
			revealPanel(html);
			return;
		}
		stepModeEnabled = false;
		currentSteps = [];
		currentStepIndex = 0;
		currentFocusedRange = undefined;
		currentFocusText = undefined;
		currentHoleContext = result["substMap"] || {};
		currentEvalResult = result["result"] || '';
		currentFinalHoleContext = currentHoleContext;
		currentFinalResult = currentEvalResult;
			currentHoleContextQueue = [];
	}

		const html = getWebviewContent(currentEvalResult || '', currentHoleContextQueue);
	revealPanel(html);
}

function getTotalStepViews(): number {
	if (!stepModeEnabled || currentSteps.length === 0) {
		return 0;
	}
	// N step items + one final state (after of the last step)
	return currentSteps.length + 1;
}

function updateStateFromStepView(index: number) {
	if (!stepModeEnabled || currentSteps.length === 0) {
		return;
	}
	currentHoleContextQueue = [];

	if (index < currentSteps.length) {
		const step = currentSteps[index];
		const beforeState = step["before"] || {};
		currentEvalResult = beforeState["result"] || '';
		currentHoleContext = beforeState["substMap"] || {};
		currentFocusedRange = step["focusedRange"];
		currentFocusText = step["focus"];
		return;
	}

	const lastStep = currentSteps[currentSteps.length - 1];
	const afterState = lastStep?.["after"] || {};
	currentEvalResult = currentFinalResult ?? (afterState["result"] || '');
	currentHoleContext = currentFinalHoleContext ?? (afterState["substMap"] || {});
	currentFocusedRange = undefined;
	currentFocusText = undefined;
}

function renderCurrentStep() {
	if (!panel) {
		return;
	}
	updateStateFromStepView(currentStepIndex);
	panel.webview.html = getWebviewContent(currentEvalResult || '', currentHoleContextQueue);
}

function moveStep(delta: number) {
	if (!stepModeEnabled || currentSteps.length === 0) {
		return;
	}
	const totalViews = getTotalStepViews();
	const newIndex = currentStepIndex + delta;
	if (newIndex < 0 || newIndex >= totalViews) {
		return;
	}
	currentStepIndex = newIndex;
	renderCurrentStep();
}

function revealPanel(html: string) {
	if (panel) {
		panel.webview.html = html;
		panel.reveal(vscode.ViewColumn.Beside);
	} else {
		panel = vscode.window.createWebviewPanel(
			'effHoleOutput',
			'effHole Output',
			vscode.ViewColumn.Beside,
			{ enableScripts: true }
		);
		panel.webview.html = html;
		panel.webview.onDidReceiveMessage(
			message => {
				switch (message.command) {
					case 'showAlert':
						vscode.window.showInformationMessage(`received：${message.text}`);
						return;
					case 'wordClicked':
						// vscode.window.showInformationMessage(`You clicked on: ${message.text}`);
						if (currentHoleContext[message.text]) {
							void logHoleClick(message.text, currentHoleContext[message.text]);
							pushHoleContextToFront(message.text, currentHoleContext[message.text]);
							reRenderPanel();
						}
						return;
					case 'holeContextHover':
						applyHoleContextHighlight(message.definition);
						return;
					case 'clearHoleContextHover':
						clearContextRowHighlight();
						return;
					case 'holeCardHover':
						applyHoleCardHighlight(message.holeName);
						return;
					case 'clearHoleCardHover':
						clearHoleCardHighlight();
						return;
					case 'prevStep':
						moveStep(-1);
						return;
					case 'nextStep':
						moveStep(1);
						return;
					case 'normalizeSelection':
						vscode.commands.executeCommand('effhole.normalizeSelection', message.text);
						return;
				}
			},
			undefined,
			extensionContext.subscriptions
		);

		panel.onDidDispose(() => {
			clearHoleContextHighlight();
			panel = undefined;
		});
	}
}

function getErrorWebviewContent(code: number, errorMessage: unknown): string {
	const htmlPath = extensionContext.asAbsolutePath('media/error.html');
	let html = fs.readFileSync(htmlPath, 'utf-8');

	let error_title = "Unknown Error";
	if (code === 1) {
		error_title = "Parsing Error";
	} else if (code === 2) {
		error_title = "Evaluation Error";
	} else if (code === 3) {
		error_title = "Fuel Exhausted";
	} else if (code === 4 || code === 5) {
		error_title = "Request Error";
	} else if (code === -2) {
		error_title = "Unknown Command";
	}

	const safeErrorMessage = typeof errorMessage === 'string' && errorMessage.trim().length > 0
		? errorMessage
		: `Backend returned status ${code} without details.`;

	html = html.replace('{{errorTitle}}', escapeHtml(error_title));
	html = html.replace('{{errorMessage}}', escapeHtml(safeErrorMessage));

	return html;
}

function isHoleContextEntry(value: unknown): value is HoleContextEntry {
	return typeof value === 'object' && value !== null && typeof (value as HoleContextEntry).value === 'string';
}

function isHoleContextMap(value: unknown): value is HoleContextMap {
	return typeof value === 'object' && value !== null && !Array.isArray(value) && Object.values(value as Record<string, unknown>).every(isHoleContextEntry);
}

function pushHoleContextToFront(holeName: string, context: HoleContextMap): void {
	const nextQueue = currentHoleContextQueue.filter(entry => entry.holeName !== holeName);
	nextQueue.unshift({ holeName, context });
	currentHoleContextQueue = nextQueue.slice(0, getHoleContextWindowSize());
}

function normalizeHoleName(name: string): string {
	const trimmed = name.trim();
	const withoutPrefix = trimmed.startsWith('{?}')
		? trimmed.slice(3)
		: trimmed.startsWith('?')
			? trimmed.slice(1)
			: trimmed;
	const underscoreIndex = withoutPrefix.indexOf('_');
	if (underscoreIndex <= 0) {
		return withoutPrefix;
	}
	return withoutPrefix.slice(0, underscoreIndex);
}

function toCodePosition(value: unknown): CodePosition | undefined {
	if (typeof value === 'object' && value !== null) {
		const maybeObj = value as { line?: unknown; column?: unknown };
		if (typeof maybeObj.line === 'number' && typeof maybeObj.column === 'number') {
			return { line: maybeObj.line, column: maybeObj.column };
		}
	}
	if (Array.isArray(value) && value.length >= 2) {
		const [line, column] = value;
		if (typeof line === 'number' && typeof column === 'number') {
			return { line, column };
		}
	}
	return undefined;
}

function computeHoleRange(content: string, start: CodePosition, rawHoleName: string): DefinitionRange {
	const startIndex = indexFromLineColumn(content, start.line, start.column);
	if (startIndex === undefined) {
		return {
			start,
			end: { line: start.line, column: start.column + 1 }
		};
	}

	const lines = content.split('\n');
	const lineText = lines[start.line - 1] ?? '';
	const columnIndex = Math.max(0, start.column - 1);
	const suffix = lineText.slice(columnIndex);
	const normalized = normalizeHoleName(rawHoleName);
	const escaped = normalized.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
	const exactPattern = escaped.length > 0
		? new RegExp(`^(?:\\{\\?\\}|\\?)${escaped}(?:_[A-Za-z0-9]+)?`)
		: undefined;
	const genericPattern = /^(?:\{\?\}|\?)[A-Za-z0-9_]+/;
	const exactMatch = exactPattern ? suffix.match(exactPattern) : null;
	const genericMatch = suffix.match(genericPattern);
	const matchedLength = Math.max(exactMatch?.[0].length ?? 0, genericMatch?.[0].length ?? 0, 1);

	return {
		start,
		end: {
			line: start.line,
			column: start.column + matchedLength,
		}
	};
}

function parseHoleDefinitions(content: string, holeMap: unknown): HoleDefinitionMap {
	if (!Array.isArray(holeMap)) {
		return {};
	}

	const definitions: HoleDefinitionMap = {};
	for (const item of holeMap) {
		if (!Array.isArray(item) || item.length < 2) {
			continue;
		}
		const start = toCodePosition(item[0]);
		const nameValue = item[1];
		if (!start || (typeof nameValue !== 'string' && typeof nameValue !== 'number')) {
			continue;
		}
		const rawName = String(nameValue);
		const normalizedName = normalizeHoleName(rawName);
		if (!normalizedName) {
			continue;
		}
		definitions[normalizedName] = computeHoleRange(content, start, rawName);
	}

	return definitions;
}

async function refreshHoleDefinitions(content: string): Promise<void> {
	currentHoleDefinitions = {};
	hoveredHoleDefinition = undefined;
	try {
		const res = await sendRequest('getHoleID', content, { showHealthGuide: false });
		if (!res || res["status"] !== 0) {
			return;
		}
		currentHoleDefinitions = parseHoleDefinitions(content, res["holeMap"]);
	} catch (error: any) {
		console.warn(`EffHole hole definition request failed: ${error.message}`);
	}
}

function renderHoleContextStack(holeContexts: HoleContextQueueEntry[]): string {
	if (holeContexts.length === 0) {
		return '<div class="hole-context-empty">Click a hole to pin its context here.</div>';
	}

	return `<div class="hole-context-stack">
		${holeContexts.map(({ holeName, context }) => {
			let rows = '';
			for (const [key, entry] of Object.entries(context)) {
				const definition = entry.definition;
				const definitionAttributes = definition
					? ` data-definition-start-line="${definition.start.line}" data-definition-start-column="${definition.start.column}" data-definition-end-line="${definition.end.line}" data-definition-end-column="${definition.end.column}"`
					: '';
				rows += `
				<tr class="hole-context-row"${definitionAttributes}>
					<td>${escapeHtml(key)}</td>
					<td>${formatHoleContextValue(entry)}</td>
				</tr>`;
			}

			return `
			<section class="hole-context-card" data-hole-name="${escapeHtml(holeName)}">
				<h3>Hole Context of ${escapeHtml(holeName)}</h3>
				<table>
					<thead>
						<tr>
							<th>Variable</th>
							<th>Value</th>
						</tr>
					</thead>
					<tbody>
						${rows}
					</tbody>
				</table>
			</section>`;
		}).join('')}
	</div>`;
}

function reRenderPanel(): void {
	if (!panel) {
		return;
	}
	panel.webview.html = getWebviewContent(currentEvalResult || '', currentHoleContextQueue);
}

function formatDefinitionRange(definition?: DefinitionRange): string {
	if (!definition) {
		return '';
	}
	return `line ${definition.start.line}, column ${definition.start.column} → line ${definition.end.line}, column ${definition.end.column}`;
}

function formatHoleContextValue(entry: HoleContextEntry): string {
	return `<pre>${processHoleContextContent(entry.value)}</pre>`;
}

function toVscodePosition(pos: unknown): vscode.Position | undefined {
	if (typeof pos !== 'object' || pos === null) {
		return undefined;
	}
	const { line, column } = pos as CodePosition;
	if (typeof line !== 'number' || typeof column !== 'number') {
		return undefined;
	}
	return new vscode.Position(Math.max(0, line - 1), Math.max(0, column - 1));
}

function toVscodeRange(definition: unknown): vscode.Range | undefined {
	if (typeof definition !== 'object' || definition === null) {
		return undefined;
	}
	const { start, end } = definition as DefinitionRange;
	const startPosition = toVscodePosition(start);
	const endPosition = toVscodePosition(end);
	if (!startPosition || !endPosition) {
		return undefined;
	}
	return new vscode.Range(startPosition, endPosition);
}

function getSourceEditors(): vscode.TextEditor[] {
	if (!currentSourceDocumentUri) {
		return [];
	}
	const targetUri = currentSourceDocumentUri.toString();
	return vscode.window.visibleTextEditors.filter(editor => editor.document.uri.toString() === targetUri);
}

function clearHoleContextHighlight(): void {
	hoveredContextDefinition = undefined;
	hoveredHoleDefinition = undefined;
	applyHoleContextDecorations();
}

function clearContextRowHighlight(): void {
	hoveredContextDefinition = undefined;
	applyHoleContextDecorations();
}

function clearHoleCardHighlight(): void {
	hoveredHoleDefinition = undefined;
	applyHoleContextDecorations();
}

function applyHoleCardHighlight(holeName: unknown): void {
	if (typeof holeName !== 'string') {
		clearHoleCardHighlight();
		return;
	}
	const normalizedName = normalizeHoleName(holeName);
	hoveredHoleDefinition = currentHoleDefinitions[normalizedName];
	applyHoleContextDecorations();
}

function applyHoleContextDecorations(): void {
	if (!holeDefinitionDecorationType) {
		return;
	}

	const ranges: vscode.Range[] = [];
	const seen = new Set<string>();
	const pushRange = (definition?: DefinitionRange) => {
		if (!definition) {
			return;
		}
		const range = toVscodeRange(definition);
		if (!range) {
			return;
		}
		const key = `${range.start.line}:${range.start.character}-${range.end.line}:${range.end.character}`;
		if (seen.has(key)) {
			return;
		}
		seen.add(key);
		ranges.push(range);
	};

	pushRange(hoveredHoleDefinition);
	pushRange(hoveredContextDefinition);

	for (const editor of getSourceEditors()) {
		editor.setDecorations(holeDefinitionDecorationType, ranges);
	}
}

function applyHoleContextHighlight(definition: unknown): void {
	if (typeof definition !== 'object' || definition === null) {
		clearContextRowHighlight();
		return;
	}
	const nextDefinition = definition as DefinitionRange;
	if (
		typeof nextDefinition.start?.line !== 'number' ||
		typeof nextDefinition.start?.column !== 'number' ||
		typeof nextDefinition.end?.line !== 'number' ||
		typeof nextDefinition.end?.column !== 'number'
	) {
		clearContextRowHighlight();
		return;
	}
	hoveredContextDefinition = nextDefinition;
	applyHoleContextDecorations();

	const range = toVscodeRange(definition);
	if (!range) {
		clearContextRowHighlight();
		return;
	}

	const editors = getSourceEditors();
	if (editors.length === 0) {
		return;
	}

	for (const editor of editors) {
		editor.revealRange(range, vscode.TextEditorRevealType.InCenterIfOutsideViewport);
	}
}

function getWebviewContent(result: string, holeContexts: HoleContextQueueEntry[]): string {
	const htmlPath = extensionContext.asAbsolutePath('media/view.html');
	let html = fs.readFileSync(htmlPath, 'utf-8');
	const totalStepViews = getTotalStepViews();
	const isLastStepView = stepModeEnabled && totalStepViews > 0 && currentStepIndex === totalStepViews - 1;
	const fuelExhaustedNotice = currentRunStatus === 3 && isLastStepView
		? `<span class="step-status step-status-warning">Fuel exhausted</span>`
		: '';
	const evalErrorNotice = currentRunStatus === 2 && isLastStepView
		? `<span class="step-status step-status-error">Evaluation error</span>`
		: '';
	const stepErrorPanel = currentRunStatus === 2 && isLastStepView
		? `<div class="step-error-panel">
			<div class="step-error-title">Evaluation error</div>
			<div class="step-error-message">${escapeHtml(currentRunErrorMessage && currentRunErrorMessage.trim().length > 0 ? currentRunErrorMessage : 'Backend returned an evaluation error without details.')}</div>
		</div>`
		: '';
	const stepControls = stepModeEnabled
		? `<div id="step-controls">
			<button id="prevStepBtn" class="vscode-button" ${currentStepIndex === 0 ? 'disabled' : ''}>Last</button>
			<button id="nextStepBtn" class="vscode-button" ${currentStepIndex >= totalStepViews - 1 ? 'disabled' : ''}>Next</button>
			<span id="step-indicator">Step ${currentStepIndex + 1}/${totalStepViews}</span>
			${fuelExhaustedNotice}
			${evalErrorNotice}
        </div>`
		: '';
	html = html.replace('{{stepControls}}', stepControls);
	html = html.replace('{{stepErrorPanel}}', stepErrorPanel);

	const highlightedOutput = highlightByFocusedRange(result, currentFocusedRange, currentFocusText);
	const formattedOutput = `<pre>${highlightedOutput}</pre>`;
	html = html.replace('{{content}}', formattedOutput);
	html = html.replace('{{content2}}', renderHoleContextStack(holeContexts));

	return html;
}

function indexFromLineColumn(text: string, line: number, column: number): number | undefined {
	if (line < 1 || column < 1) {
		return undefined;
	}
	const lines = text.split('\n');
	if (line > lines.length) {
		return undefined;
	}
	let index = 0;
	for (let i = 0; i < line - 1; i++) {
		index += lines[i].length + 1;
	}
	const targetLine = lines[line - 1];
	if (column - 1 > targetLine.length) {
		return undefined;
	}
	return index + (column - 1);
}

function computeRangeBounds(text: string, focusedRange: any, focusText?: string): [number, number] | undefined {
	if (!focusedRange?.start || !focusedRange?.end) {
		return undefined;
	}
	const start = indexFromLineColumn(text, focusedRange.start.line, focusedRange.start.column);
	const endRaw = indexFromLineColumn(text, focusedRange.end.line, focusedRange.end.column);
	if (start === undefined || endRaw === undefined) {
		return undefined;
	}

	const exclusiveEnd = Math.min(Math.max(endRaw, start + 1), text.length);
	const inclusiveEnd = Math.min(Math.max(endRaw + 1, start + 1), text.length);

	if (focusText && focusText.length > 0) {
		const exSlice = text.slice(start, exclusiveEnd);
		const inSlice = text.slice(start, inclusiveEnd);
		if (exSlice === focusText) {
			return [start, exclusiveEnd];
		}
		if (inSlice === focusText) {
			return [start, inclusiveEnd];
		}
	}

	if (exclusiveEnd > start) {
		return [start, exclusiveEnd];
	}
	if (inclusiveEnd > start) {
		return [start, inclusiveEnd];
	}
	return undefined;
}

function highlightByFocusedRange(text: string, focusedRange: any, focusText?: string): string {
	if (!stepModeEnabled) {
		return processContent(text);
	}
	const bounds = computeRangeBounds(text, focusedRange, focusText);
	if (!bounds) {
		return processContent(text);
	}
	const [start, end] = bounds;
	const before = text.slice(0, start);
	const focus = text.slice(start, end);
	const after = text.slice(end);
	if (focus.length === 0) {
		return processContent(text);
	}

	return `${processContent(before)}<span class="step-focus">${processContent(focus)}</span>${processContent(after)}`;
}

function processContent(text: string): string {
	let safeContent = escapeHtml(text);
	// Transform specific words into clickable spans
	// Match strings like "?12_34" or "{?}1_23"
	return safeContent.replace(/(?:\?|\{\?\})(\d+_\d+)/g, (match, id) => {
		return `<span class="interactive-word" data-word="${id}">${match}</span>`;
	});
}

function processHoleContextContent(text: string): string {
	return processContent(text).replace(/\$/g, '<span class="continuation-param">$</span>');
}

function escapeHtml(input: unknown): string {
	const s = input === undefined || input === null ? '' : String(input);
	return s.replace(/[&<>"']/g, c => ({
		'&': '&amp;',
		'<': '&lt;',
		'>': '&gt;',
		'"': '&quot;',
		"'": '&#39;',
	}[c]!));
}

// This method is called when your extension is deactivated
export function deactivate() { }
