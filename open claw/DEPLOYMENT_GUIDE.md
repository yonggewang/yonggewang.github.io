# Professional Deployment Guide: OpenClaw + Qwen 3.5

This guide provides a turnkey solution for deploying a high-performance, private AI agent system on a new Mac using OpenClaw and the Qwen 3.5-35B Model (MLX optimized).

## 🖥️ Hardware Requirements

- **Apple Silicon Mac**: M1 Pro/Max, M2 Pro/Max, M3, or M4.
- **Unified Memory (RAM)**: 
    - **Recommended**: 32GB or more (for smooth operation of the 35B MoE model).
    - **Minimum**: 24GB.
- **Disk Space**: At least 30GB free for the model and environment.

## 🚀 Installation Steps (Starting from Zero)

### 1. Run the Setup Script
Open your terminal and run the following command to download and execute the automated setup script:

```bash
# Create a workspace
mkdir -p ~/openclaw-llm && cd ~/openclaw-llm

# Run the setup script
bash <(curl -s -L https://raw.githubusercontent.com/your-repo/path/to/setup_openclaw_qwen.sh)
```
*(Note: For now, you can copy the `setup_openclaw_qwen.sh` file provided or host it on your GitHub/Server.)*

### 2. What the Script Does
- Installs **Homebrew**, **Node.js**, and **Python**.
- Downloads the **Qwen 3.5-35B-A3B** 4-bit quantized model (optimized for speed).
- Configures **OpenClaw** with the "Brain-Transplant" settings verified for local-only operation.
- Sets up a **128,000 token** context window.
- **Pre-installs Essential Plugins**: Automatically enables Email, Slack, Teams, and Web Search integrations.
- **Configures Auto-Start**: Installs macOS `LaunchAgents` so the AI server and OpenClaw gateway start completely silently in the background every time the Mac boots.

## 🛠️ Operating the System

Because the setup installs background `LaunchAgents`, **you do not need to manually start any servers!** They are always running and ready.

### Interaction
Whenever you want to talk to the agent, simply open a terminal and type:
```bash
openclaw tui
```

### Visual Dashboard (Canvas)
You can also view the agent's thought process, files, and chat UI by opening your browser to:
👉 **[http://localhost:18789/__openclaw__/canvas/](http://localhost:18789/__openclaw__/canvas/)**

## 🔒 Security & Privacy
- **100% Local**: No data leaves the machine. No API keys from OpenAI or Anthropic are required.
- **Encrypted Gateway**: Uses a local token-based protocol for secure channel connections.

## 🛠️ Troubleshooting
- **Missing Xcode Tools**: If prompted, click "Install" when the terminal asks for Command Line Tools.
- **Port 1234 in use**: Ensure no other LLM servers are running.
- **RAM Pressure**: If the system is sluggish, close browser tabs or other memory-heavy apps.
