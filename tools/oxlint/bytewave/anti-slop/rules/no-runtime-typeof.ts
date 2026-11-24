import { defineRule } from "@oxlint/plugins";

import type { ESTree, SourceCode } from "@oxlint/plugins";

type RuntimeFunction = ESTree.ArrowFunctionExpression | ESTree.Function;

function isRuntimeFunction(node: ESTree.Node): node is RuntimeFunction {
	return (
		node.type === "ArrowFunctionExpression" ||
		node.type === "FunctionDeclaration" ||
		node.type === "FunctionExpression"
	);
}

function isInsideTypeGuard(node: ESTree.Node, sourceCode: SourceCode, filename: string): boolean {
	let current: ESTree.Node | null = node.parent;
	while (current !== null && current.type !== "Program") {
		if (isRuntimeFunction(current)) {
			if (current.returnType?.typeAnnotation.type === "TSTypePredicate") return true;
			if (!/\.[cm]?js$/u.test(filename) || current.type !== "FunctionDeclaration") return false;
			const owner = current.parent.type === "ExportNamedDeclaration" ? current.parent : current;
			const comment = sourceCode.getCommentsBefore(owner).at(-1);
			if (comment?.type !== "Block" || !comment.value.startsWith("*")) return false;
			const predicate = /@returns?\s*\{\s*([A-Za-z_$][\w$]*)\s+is\s+([^{}]+)\}/u.exec(comment.value);
			return predicate !== null && current.params.some(
				(parameter) => parameter.type === "Identifier" && parameter.name === predicate[1],
			);
		}
		current = current.parent;
	}
	return false;
}

/** Disallow runtime typeof checks that narrow unparsed values instead of decoding them. */
export const noRuntimeTypeofRule = defineRule({
	meta: {
		type: "problem",
		docs: {
			description:
				"Disallow runtime typeof checks; external values must be decoded into meaningful types at their I/O boundary.",
		},
		messages: {
			runtimeTypeof:
				"A `typeof` check narrows a representation without establishing its contract. Parse input at its I/O boundary, then branch on the domain value.",
		},
		schema: [
			{
				type: "object",
				properties: {
					allowInTypeGuards: { type: "boolean" },
				},
				additionalProperties: false,
			},
		],
		defaultOptions: [{ allowInTypeGuards: false }],
	},
	createOnce(context) {
		return {
			UnaryExpression(node) {
				const option = context.options?.[0];
				const allowInTypeGuards =
					typeof option === "object" &&
					option !== null &&
					!Array.isArray(option) &&
					option.allowInTypeGuards === true;
				if (
					node.operator === "typeof" &&
					(!allowInTypeGuards || !isInsideTypeGuard(node, context.sourceCode, context.filename))
				) {
					context.report({ node, messageId: "runtimeTypeof" });
				}
			},
		};
	},
});
