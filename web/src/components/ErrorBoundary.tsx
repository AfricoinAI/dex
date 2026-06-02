import { Component, type ErrorInfo, type ReactNode } from "react";

type Props = {
  children: ReactNode;
  label?: string;
  // Optional custom fallback. Receives the caught error and a reset callback.
  // When provided, replaces the default error card.
  fallback?: (error: Error, reset: () => void) => ReactNode;
};
type State = { error: Error | null };

// A component crash anywhere below this boundary stops here instead of
// blanking the whole page. The fallback shows the real error message so
// the root cause is visible rather than swallowed.
export class ErrorBoundary extends Component<Props, State> {
  state: State = { error: null };

  static getDerivedStateFromError(error: Error): State {
    return { error };
  }

  componentDidCatch(error: Error, info: ErrorInfo) {
    // eslint-disable-next-line no-console
    console.error(`[${this.props.label ?? "ErrorBoundary"}]`, error, info);
  }

  render() {
    const { error } = this.state;
    if (!error) return this.props.children;
    if (this.props.fallback) return this.props.fallback(error, () => this.setState({ error: null }));
    return (
      <main className="shell">
        <section className="card">
          <div className="head">
            <div className="title">
              {this.props.label ? `${this.props.label} crashed` : "Something broke"}
            </div>
          </div>
          <div className="box">
            <div className="lbl">
              <span>The rest of the app should still work — this section crashed at render.</span>
            </div>
            <div className="status err">{error.message || String(error)}</div>
          </div>
          <button className="cta" onClick={() => this.setState({ error: null })}>
            Retry
          </button>
          <div className="status">
            Or{" "}
            <a
              href="#"
              onClick={(e) => {
                e.preventDefault();
                location.reload();
              }}
            >
              reload the page
            </a>
            .
          </div>
        </section>
      </main>
    );
  }
}
