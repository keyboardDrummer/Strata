FROM ubuntu:24.04

ARG DEBIAN_FRONTEND=noninteractive

# Install base dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl wget git ca-certificates unzip python3 python3-pip pipx \
    && rm -rf /var/lib/apt/lists/*

# Install Node.js (needed for Claude Code and Kiro CLI)
RUN curl -fsSL https://deb.nodesource.com/setup_22.x | bash - \
    && apt-get install -y nodejs \
    && rm -rf /var/lib/apt/lists/*

# Install elan (Lean version manager) and the toolchain specified in lean-toolchain
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | bash -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"

# Install cvc5 (required by Strata tests)
RUN ARCH=$(uname -m) \
    && if [ "$ARCH" = "x86_64" ]; then ARCH_NAME="x86_64"; \
       elif [ "$ARCH" = "aarch64" ] || [ "$ARCH" = "arm64" ]; then ARCH_NAME="arm64"; \
       else echo "Unsupported architecture: $ARCH" && exit 1; fi \
    && wget -q https://github.com/cvc5/cvc5/releases/download/cvc5-1.2.1/cvc5-Linux-${ARCH_NAME}-static.zip \
    && unzip -q cvc5-Linux-${ARCH_NAME}-static.zip \
    && mv cvc5-Linux-${ARCH_NAME}-static/bin/cvc5 /usr/local/bin/ \
    && rm -rf cvc5-Linux-${ARCH_NAME}-static*

# Install z3 (required by Strata tests)
RUN ARCH=$(uname -m) \
    && if [ "$ARCH" = "x86_64" ]; then \
         wget -q https://github.com/Z3Prover/z3/releases/download/z3-4.15.2/z3-4.15.2-x64-glibc-2.39.zip \
         && unzip -q z3-4.15.2-x64-glibc-2.39.zip \
         && mv z3-4.15.2-x64-glibc-2.39/bin/z3 /usr/local/bin/ \
         && rm -rf z3-4.15.2-x64-glibc-2.39*; \
       elif [ "$ARCH" = "aarch64" ] || [ "$ARCH" = "arm64" ]; then \
         wget -q https://github.com/Z3Prover/z3/releases/download/z3-4.15.2/z3-4.15.2-arm64-glibc-2.34.zip \
         && unzip -q z3-4.15.2-arm64-glibc-2.34.zip \
         && mv z3-4.15.2-arm64-glibc-2.34/bin/z3 /usr/local/bin/ \
         && rm -rf z3-4.15.2-arm64-glibc-2.34*; \
       else echo "Unsupported architecture: $ARCH" && exit 1; fi

# Install Claude Code CLI
RUN npm install -g @anthropic-ai/claude-code

# Install Kiro CLI
RUN npm install -g kiro

# Install uv (needed for lean-lsp-mcp via uvx)
RUN pipx install uv
ENV PATH="/root/.local/bin:${PATH}"

WORKDIR /workspaces/Strata
