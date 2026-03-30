# QCP: A Practical Separation Logic-based C Program Verification Tool

## File Structure
- `linux-binary/`, `win-binary/`, `mac-arm64-binary`: Precompiled QCP binaries
- `QCP_examples/`: Annotated C programs
- `SeparationLogic/`: Rocq scripts to check QCP-generated VCs
- `tutorial/`: Step-by-step QCP usage guide
- `run-example-linux.sh`, `run-example-windows.sh`: Scripts to run QCP examples
- `mcp/`: QCP-mcp and Rocq-mcp files
- `qide.vsix` : QCP VSCode Extension

## Environment Setup

We provide two environment setup options:

1. Non-Docker local environment setup (build and run directly on your host machine).
2. Docker-based environment setup (recommended for reproducibility).

You can choose either option according to your needs.

### Local Environment Setup

#### Prerequisites
- Rocq 8.20.1 (Coq 8.20.1), recommended with OCaml 4.14.1

Optional (only if you use MCP locally):
- `uv` (for `qcp-mcp` / `rocq-mcp` Python environment)
- `opam` + `coq-lsp` (for `rocq-mcp` interactive tools)

#### Configure Setup

To compile generated Rocq files in `SeparationLogic/`, create `CONFIGURE` (no extension) in both:

- `SeparationLogic/CONFIGURE`
- `SeparationLogic/unifysl/CONFIGURE`

Example `CONFIGURE` content:

```ini
COQBIN = /absolute/path/to/coq/bin/
# Windows users: set SUF to .exe
# SUF = .exe
```
#### Rocq Files Build

Then you can compile Rocq files:

```bash
cd SeparationLogic/unifysl
make depend && make
cd ..
make depend && make
```

### Docker Environment Setup

#### Prerequisites

- Docker installed ([Get Docker](https://docs.docker.com/get-docker/))
- Visual Studio Code ([Download](https://code.visualstudio.com/))
- VS Code Remote - Containers extension ([Install](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers))

#### Build the Docker Image

Open a terminal in the project root and run:

```sh
docker build --build-arg MAKE_JOBS=5 -t qcp .
```

This will build the Docker image using the provided `Dockerfile`.

#### Run VS Code Devcontainer

1. Check the `.devcontainer/devcontainer.json` file exists in the project root.
2. Open the project root folder in VS Code.
3. When prompted, click "Reopen in Container" or use the command palette:
   - `Ctrl+Shift+P` → "Dev Containers: Reopen in Container"
4. VS Code will build the container and set up the environment automatically.

## QIDE Extension

### Setup

The QIDE extension for VS Code should be automatically installed and configured when using the devcontainer setup. If not, follow these steps:

- Install the QIDE extension from the VS Code UI.
  (Note that we did not publish the extension to the marketplace, so do not search for it in the extensions shop.)
  - Open the command palette (`Ctrl+Shift+P`)
  - Select "Extensions: Install from VSIX..."
  - Choose the VSIX file `qide.vsix` from the project root.
- QIDE extension settings: open `File > Preferences > Settings`, search for `qide`, and set:
  - `qide.lspBinPath` to the path of the QCP binary (e.g., `linux-binary/lsp`)
  - `qide.lspArg` is the excution options for QCP. You can leave it empty refer to `Options to run QCP`.

### Usage

- Open an annotated C program.
- Move the cursor to any place you like and press `Alt+Rightarrow`.
  You can change the keyboard shortcuts settings if needed.
  You can also run the command `qide.interpretToPoint` directly from the command palette (`Ctrl+Shift+P`).

### QCP Command-Line Tool

The `run-example-linux.sh` and `run-example-windows.sh` scripts in the root directory give examples of how to run QCP command-line tool. You can directly execute them if you have the required environment set up.

Below is a summary of the main command-line options of QCP. We also recommend following the tutorials in the `tutorial/` folder for a comprehensive guide.

**Usage:**
```
linux_binary/symexec [options]
```

**Required options:**
- `--input-file=<file>`: Specify the input C source code.
- `--goal-file=<file>`: Output file for generated verification conditions (VCs).
- `--proof-auto-file=<file>`: Output file for automatically solved VCs.
- `--proof-manual-file=<file>`: Output file for VCs requiring manual proofs.

**Optional flags:**
- `--gen-and-backup`: If output files exist, back them up before overwriting; otherwise, only "proof-manual" is backed up.
- `--no-exec-info`: Suppress intermediate information during symbolic execution.
- `--coq-logic-path=<path>`: Specify the Coq logic path for the goal file.
- `-slp <dir> <path>`: Add a directory to the strategy search paths.
- `-I<dir>`: Add a directory to the include search paths.

**Preprocessing:**
If your C source uses preprocessor directives (`#define`, `#include`, etc.), preprocess it first:
```
cpp -C <input-file> <output-file>
```
Note: Only `#include` is natively supported.

**Coq Integration:**
The generated `.v` files must be used with SeparationLogic. For details, see `SeparationLogic/README.md`.

## MCP Setup

The `mcp/rocq-mcp` directory is a git submodule. Before configuring MCP, make sure submodule content is initialized and up to date.

From the project root:

```bash
# Initialize and update submodules
git submodule sync --recursive
git submodule update --init --recursive
```

After updating submodules, verify `mcp/rocq-mcp/README.md` exists.

If you do not install uv, you can use the following command to install : 
```bash
# On macOS and Linux.
curl -LsSf https://astral.sh/uv/install.sh | sh

# On Windows.
powershell -ExecutionPolicy ByPass -c "irm https://astral.sh/uv/install.ps1 | iex"
```

### 1) Configure `qcp-mcp`

```bash
cd mcp/qcp-mcp
uv venv .venv
uv tool install .
```

Set `mcp/qcp-mcp/CONFIGURE`:

```ini
QCP_MCP_BIN=/absolute/path/to/qcp/mcp/binary
```

### 2) Configure `rocq-mcp`

Install and prepare in submodule:


```bash
cd mcp/rocq-mcp
uv tool install ".[interactive]"
```

`rocq-mcp` interactive tools rely on `pet` from `coq-lsp`. We recommend installing `coq-lsp` via `opam`.

Linux (Ubuntu/Debian example):

```bash
sudo apt update
sudo apt install -y opam bubblewrap
opam init -y
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install -y coq-lsp
pet --version
```

macOS (Homebrew example):

```bash
brew install opam
opam init -y
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install -y coq-lsp
pet --version
```

Windows:

- Recommended: use WSL2 (Ubuntu), then run the Linux commands above.
- Native Windows opam setup is possible but less stable for this workflow.

### 3) IDE Setup

**VSCode Copilot**

Create or edit `.vscode/mcp.json` in the project root.

Linux/macOS example:

```json
{
  "servers": {
    "qcp": {
      "type": "stdio",
      "command": "/absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/.venv/bin/python",
      "args": [
        "/absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/server.py"
      ]
    },
    "rocq-mcp": {
      "type": "stdio",
      "command": "rocq-mcp",
      "env": {
        "ROCQ_WORKSPACE": "${workspaceFolder}"
      }
    }
  }
}
```

After editing `mcp.json`, enable/start the servers from VS Code MCP server list.


**Claude Code**

Add servers in terminal:

```bash
claude mcp add -s project qcp -- /absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/.venv/bin/python /absolute/path/to/qcp-binary-democases/mcp/qcp-mcp/server.py
claude mcp add -s project rocq-mcp -- rocq-mcp
```

Platform-specific config file locations (if you prefer manual JSON editing):

- Linux: `~/.config/claude/`
- macOS: `~/Library/Application Support/Claude/`


For more details, refer to:
- `mcp/qcp-mcp/README.md`
- `mcp/rocq-mcp/README.md`


## Evaluation

Our evaluation consists of two parts: the Tool component and the VSCode Extension component. 
- The Tool component allows you to check files in the ``QCP_examples`` by running ``sh ./run-example-linux.sh``, and it generates the corresponding Coq files in the ``SeparationLogic/examples/`` directory. 
- The VSCode Extension component is designed to support real-time verification interaction. You can open any annotated C file to view the current assertion state, which facilitates the continued writing of annotations for proofs.