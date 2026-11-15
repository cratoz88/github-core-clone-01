import { createApp } from "./app.ts";
import type { Server } from "node:http";

// Entrypoint for the make.fun trial: start the forge on an ephemeral
// port, tell the trial environment which port that is, then stay up
// until the environment reports that the grading run is finished.

const REQUEST_TIMEOUT_MS = 30_000;
const FIRST_RETRY_MS = 250;
const MAX_RETRY_MS = 2_000;
const DONE_POLL_MS = 500;

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

function envBaseUrl(): string {
  const raw = (process.env.MAKEFUN_ENV_URL ?? "").trim();
  const base = raw.replace(/\/+$/, "");
  if (!base) {
    console.error("MAKEFUN_ENV_URL is not set");
    process.exit(1);
  }
  return base;
}

function nextDelay(current: number): number {
  return Math.min(current * 2, MAX_RETRY_MS);
}

async function register(base: string, port: number): Promise<void> {
  let delay = FIRST_RETRY_MS;
  for (;;) {
    let response: Response | null = null;
    try {
      response = await fetch(`${base}/register`, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({ port }),
        signal: AbortSignal.timeout(REQUEST_TIMEOUT_MS),
      });
    } catch (error) {
      console.log(
        `register request failed (${error instanceof Error ? error.message : String(error)}), retrying in ${delay}ms`,
      );
      await sleep(delay);
      delay = nextDelay(delay);
      continue;
    }

    if (response.status === 200 || response.status === 409) {
      console.log(
        response.status === 409
          ? `register answered 409 (already registered), continuing on port ${port}`
          : `registered on port ${port}`,
      );
      return;
    }
    if (response.status === 400 || response.status === 405) {
      throw new Error(`register rejected with status ${response.status}`);
    }
    console.log(
      `register returned status ${response.status}, retrying in ${delay}ms`,
    );
    await sleep(delay);
    delay = nextDelay(delay);
  }
}

async function waitForDone(base: string): Promise<void> {
  let delay = FIRST_RETRY_MS;
  for (;;) {
    let response: Response | null = null;
    try {
      response = await fetch(`${base}/done`, {
        signal: AbortSignal.timeout(REQUEST_TIMEOUT_MS),
      });
    } catch (error) {
      console.log(
        `done check failed (${error instanceof Error ? error.message : String(error)}), retrying in ${delay}ms`,
      );
      await sleep(delay);
      delay = nextDelay(delay);
      continue;
    }

    if (!response.ok) {
      console.log(
        `done check returned status ${response.status}, retrying in ${delay}ms`,
      );
      await sleep(delay);
      delay = nextDelay(delay);
      continue;
    }

    let body: unknown = null;
    try {
      body = await response.json();
    } catch {
      console.log("done check returned unreadable JSON, retrying");
      await sleep(delay);
      delay = nextDelay(delay);
      continue;
    }

    if (
      typeof body === "object" &&
      body !== null &&
      (body as { done?: unknown }).done === true
    ) {
      console.log("trial finished");
      return;
    }

    // A healthy answer while the suite is still running; reset the
    // failure backoff and poll again shortly.
    delay = FIRST_RETRY_MS;
    await sleep(DONE_POLL_MS);
  }
}

async function startServer(): Promise<{ server: Server; port: number }> {
  const server = createApp();
  const port = await new Promise<number>((resolve, reject) => {
    server.once("error", reject);
    server.listen(0, () => {
      const address = server.address();
      if (!address || typeof address === "string") {
        reject(new Error("could not determine the bound port"));
        return;
      }
      resolve(address.port);
    });
  });
  return { server, port };
}

async function main(): Promise<void> {
  const base = envBaseUrl();
  const { server, port } = await startServer();
  console.log(`forge listening on port ${port}`);

  try {
    await register(base, port);
    console.log("waiting for the trial to finish");
    await waitForDone(base);
  } catch (error) {
    console.error(
      `fatal error: ${error instanceof Error ? error.message : String(error)}`,
    );
    server.close(() => process.exit(1));
    return;
  }

  console.log("shutting down");
  server.close(() => process.exit(0));
}

main().catch((error: unknown) => {
  console.error(
    `fatal error: ${error instanceof Error ? error.message : String(error)}`,
  );
  process.exit(1);
});
