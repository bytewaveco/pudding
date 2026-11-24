import { defineRule } from "@oxlint/plugins";
import type { ESTree, SourceCode } from "@oxlint/plugins";

type Parameter = ESTree.ParamPattern;
type ParameterOwner =
  | ESTree.ArrowFunctionExpression
  | ESTree.Function
  | ESTree.TSCallSignatureDeclaration
  | ESTree.TSConstructSignatureDeclaration
  | ESTree.TSConstructorType
  | ESTree.TSFunctionType
  | ESTree.TSMethodSignature;

function parameterAnnotation(parameter: Parameter): ESTree.TSTypeAnnotation | null | undefined {
  if (parameter.type === "TSParameterProperty") {
    return parameterAnnotation(parameter.parameter);
  }
  if (parameter.type === "RestElement") {
    return parameter.typeAnnotation ?? parameterAnnotation(parameter.argument);
  }
  if (parameter.type === "AssignmentPattern") {
    return parameter.typeAnnotation ?? parameter.left.typeAnnotation;
  }
  return parameter.typeAnnotation;
}

function parameterName(parameter: Parameter, sourceText: string): string {
  if (parameter.type === "TSParameterProperty") {
    return parameterName(parameter.parameter, sourceText);
  }
  if (parameter.type === "AssignmentPattern") {
    return parameterName(parameter.left, sourceText);
  }
  if (parameter.type === "RestElement") {
    return parameterName(parameter.argument, sourceText);
  }
  return parameter.type === "Identifier"
    ? parameter.name
    : sourceText.replace(/\s*:\s*unknown\s*$/u, "");
}

/** Keep untrusted inputs inside decoding and serialization boundaries until they are parsed. */
function isParsedBoundary(
  sourceCode: SourceCode,
  owner: ParameterOwner,
  parameter: Parameter,
): boolean {
  if (parameter.type !== "Identifier") return false;
  const variable = sourceCode.getDeclaredVariables(owner).find(
    (entry) => entry.identifiers.includes(parameter),
  );
  if (!variable || variable.references.length === 0) return false;
  let parsed = false;
  for (const reference of variable.references) {
    if (reference.isWrite()) return false;
    let argument: ESTree.Node = reference.identifier;
    let ancestor: ESTree.Node | null = argument.parent;
    while (ancestor !== null && ancestor !== owner) {
      if (
        ancestor.type === "ArrowFunctionExpression" ||
        ancestor.type === "FunctionDeclaration" ||
        ancestor.type === "FunctionExpression"
      ) return false;
      ancestor = ancestor.parent;
    }
    if (ancestor !== owner) return false;
    const fallback = argument.parent;
    if (
      fallback.type === "LogicalExpression" && fallback.operator === "??" &&
      fallback.left === argument && fallback.right.type === "ObjectExpression" &&
      fallback.right.properties.length === 0
    ) argument = fallback;
    const call = argument.parent;
    if (
      call.type !== "CallExpression" || call.optional || call.arguments[0] !== argument ||
      call.callee.type !== "MemberExpression" || call.callee.computed || call.callee.optional ||
      call.callee.property.type !== "Identifier"
    ) return false;
    const method = call.callee.property.name;
    if (method === "parse" || method === "safeParse") {
      parsed = true;
      continue;
    }
    if (
      method !== "stringify" || call.callee.object.type !== "Identifier" ||
      call.callee.object.name !== "JSON" || !sourceCode.isGlobalReference(call.callee.object)
    ) return false;
  }
  return parsed;
}

/** Disallow unknown inputs except parsing boundaries and explicitly named error-cause enrichment. */
export const noUnknownParametersRule = defineRule({
  meta: {
    type: "problem",
    docs: {
      description:
        "Disallow unknown function parameters except `cause` and inputs used exclusively by parsers and JSON serialization.",
    },
    messages: {
      unknownParameter:
        "Parameter `{{parameter}}` leaves input unparsed. Accept a named domain type; run the expected schema or parser at the I/O boundary before calling this function.",
    },
  },
  createOnce(context) {
    const checkParameters = (node: ParameterOwner) => {
      for (const parameter of node.params) {
        const annotation = parameterAnnotation(parameter);
        if (annotation?.typeAnnotation.type !== "TSUnknownKeyword") continue;
        const name = parameterName(parameter, context.sourceCode.getText(parameter));
        if (name === "cause" || isParsedBoundary(context.sourceCode, node, parameter)) continue;
        context.report({
          node: annotation.typeAnnotation,
          messageId: "unknownParameter",
          data: { parameter: name },
        });
      }
    };

    return {
      ArrowFunctionExpression: checkParameters,
      FunctionDeclaration: checkParameters,
      FunctionExpression: checkParameters,
      TSCallSignatureDeclaration: checkParameters,
      TSConstructSignatureDeclaration: checkParameters,
      TSConstructorType: checkParameters,
      TSDeclareFunction: checkParameters,
      TSEmptyBodyFunctionExpression: checkParameters,
      TSFunctionType: checkParameters,
      TSMethodSignature: checkParameters,
    };
  },
});
