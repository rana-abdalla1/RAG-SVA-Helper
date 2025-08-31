# RAG-SVA-Helper
Please note that this is just me playing around and is very much a work in progress with minimal features.
I used the open source dataset VERT which containts verilog code along with SVA's for my vector store. I've only done minimal processing and I'm sure with slightly more nuanced cleaning, retrieval from the vector store will yield much more useful results. 
Uses a few-shot prompting with explicit SVA rules for better assertion generation. 

## Features
- Loads requirements and code examples from a JSONL file.
- Embeds and stores documents using OpenAI embeddings and Chroma.
- Retrieves relevant exemplars for a given requirement.
- Uses a prompt template and LLM to generate strict SVA and anti-vacuity cover properties.
- Pretty-prints the generated assertions and notes.

## Requirements
- Python 3.8+
- Jupyter Notebook
- Packages: `langchain==0.3.0`, `langchain-community==0.3.0`, `langchain-openai==0.2.0`, `chromadb`, `openai`, `tiktoken`

## Usage
1. Install dependencies (see the first cell in the notebook for pip commands).
2. Place your `VERT.json` file in the appropriate path (update the path in the notebook if needed).
3. Open and run the notebook `Light_RAG_SVA_Vert_Colab.ipynb` step by step.
4. Modify the requirement and signals in the example cell to generate custom SVAs.

## Example
```
resp = generate_sva(
    requirement="When valid is high and ready is low, data must remain stable until ready goes high.",
    signals={"valid":"valid","ready":"ready","data":"data[7:0]"},
    clock="clk", reset="rst_n"
)
display_sva(resp)
```
## Example Output (Not great but getting there)

------------------------------------------------------------
ASSERTION
------------------------------------------------------------
property data_stable_until_ready; @(posedge clk) disable iff (!rst_n) (valid && !ready) |-> $stable(data) until_with (ready); endproperty assert property (data_stable_until_ready);

------------------------------------------------------------
ANTI-VACUITY COVER
------------------------------------------------------------
cover property (@(posedge clk) disable iff (!rst_n) (valid && !ready) ##[1:$] ready);

------------------------------------------------------------
NOTES
------------------------------------------------------------
- Overlapped |-> starts stability on the first stall cycle.
- until_with includes the release (READY) cycle.


### Additional examples from 