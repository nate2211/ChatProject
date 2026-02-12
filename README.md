# PromptChat

PromptChat is a modular, pipeline-based data ingestion and AI processing engine. It allows users to chain together discrete functional "blocks" to perform advanced web scraping, local code analysis, network packet ingestion, and RAG (Retrieval-Augmented Generation) using both local and remote AI models.

Built with an "Intelligence-First" philosophy, PromptChat doesn't just fetch data; it extracts lexicons, tracks cross-document similarities, and uncovers hidden assets through advanced sniffing and automated media processing.

---

## 🚀 Key Capabilities

### 🛠 Modular Pipeline Architecture
- **Block-Based Workflows:** Chain blocks like `webcorpus`, `localcodecorpus`, `intelligence`, and `chat` to build custom AI agents.
- **Subpipelines:** Process data *within* a block. For example, use a subpipeline to clean search queries or fix grammar before the final model sees the text.
- **Memory Store:** A persistent JSON-based memory that shares URLs, extracted lexicons, and "intelligence" concepts across different pipeline runs.

### 🔍 Advanced Web & Media Discovery
- **Hybrid Scraping:** Combines `Trafilatura` for clean text extraction with `Playwright/Camoufox` to handle JS-heavy sites and bypass bot detection.
- **Deep Sniffing:** Integrated `NetworkSniffer`, `JSSniffer`, `ReactSniffer`, `DatabaseSniffer`, and `InteractionSniffer` to find hidden API endpoints, manifest files (HLS/DASH), and internal SPA routes.
- **Reverse Image/Video Search:** Provide a local image or video; the engine extracts frames (via FFmpeg), generates a visual signature, and finds original sources or mirrors via SearXNG.

### 💻 Technical & Code Intelligence
- **AST-Based Indexing:** Scans local directories and uses Abstract Syntax Trees to index Python functions and classes as individual searchable units rather than large, messy files.
- **CodeSearch:** Specialized SQLite FTS5 logic designed for technical retrieval, prioritizing API identifiers, dotted method names, and imports.

### 🤖 Local AI & Model Flexibility
- **Lexicon Models:** Local, deterministic models that weave discovered terms into replies—perfect for highly technical or domain-specific tasks without API costs.
- **Hugging Face Integration:** Support for local `transformers` models (Flan-T5, GPT-2, etc.) for summarization, NER, and classification through `TensorBlock`.

---

## 📦 Installation

### Prerequisites
- **Python 3.10+**
- **FFmpeg:** Required for video frame extraction and HLS processing.
- **Playwright Browsers:** Chromium or Firefox.

### Setup
1. **Clone the repository:**
   ```bash
   git clone [https://github.com/yourusername/promptchat.git](https://github.com/yourusername/promptchat.git)
   cd promptchat

    Install dependencies:
    Bash

    pip install -r requirements.txt

    Install Playwright binaries:
    Bash

    playwright install chromium firefox

⚙️ Configuration

Create a .env file in the root directory to enable external integrations:
Code snippet

GOOGLE_API_KEY=your_key_here    # Required for YouTube/Google CSE
GOOGLE_CSE_ID=your_id_here      # Required for Google Search

🛠 Usage
Running the GUI

The primary way to interact with PromptChat is via the PyQt5 interface:
Bash

python gui.py

    Prompt Chat Tab: Build and run pipelines, manage extras, and view real-time logs.

    Database Tab: Explore cached web pages, code snippets, and discovered links.

    Log Tab: Search and filter real-time debug information from the async engine.

CLI Example
Bash

python main.py --pipeline "webcorpus|prompt|chat" --extra webcorpus.query="latest rust programming news"

