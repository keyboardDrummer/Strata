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

# Install Claude Code CLI
RUN npm install -g @anthropic-ai/claude-code

# Install Kiro CLI
RUN npm install -g kiro

# Install uv (needed for lean-lsp-mcp via uvx)
RUN pipx install uv
ENV PATH="/root/.local/bin:${PATH}"

WORKDIR /workspaces/Strata
