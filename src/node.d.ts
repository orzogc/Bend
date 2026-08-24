// The host calls this compiler makes. The repo has no dependencies,
// so it declares them instead of installing @types/node.
declare module "fs" {
  export function readFileSync(path: string | URL, enc: "utf8"): string;
  export function writeFileSync(path: string | URL, data: string): void;
  export function realpathSync(path: string): string;
}
declare const process: { argv: string[]; exit(code?: number): never };
