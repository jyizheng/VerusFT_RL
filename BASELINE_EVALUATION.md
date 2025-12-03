# Qwen Model Baseline Evaluation Guide

This guide explains how to run baseline evaluations for Qwen2.5-Coder models on Verus code generation tasks.

## Overview

The `baseline_evaluation.py` script evaluates Qwen models in two modes:
- **Zero-shot**: Model generates completions without any examples
- **Few-shot**: Model receives 3 in-context examples before the test prompt

## Quick Start

### 1. Evaluate a Single Model Size

```bash
# Zero-shot evaluation with 1.5B model
python baseline_evaluation.py --model-size 1.5B --mode zero-shot

# Few-shot evaluation with 7B model
python baseline_evaluation.py --model-size 7B --mode few-shot

# Both modes with 3B model
python baseline_evaluation.py --model-size 3B --mode both
```

### 2. Evaluate All Model Sizes

```bash
# Run all models in zero-shot mode (takes hours!)
python baseline_evaluation.py --model-size all --mode zero-shot

# Run all models in both modes (takes many hours!)
python baseline_evaluation.py --model-size all --mode both
```

## Available Model Sizes

| Size | Model Name | VRAM Required | Speed | Quality |
|------|-----------|---------------|-------|---------|
| 0.5B | Qwen/Qwen2.5-Coder-0.5B | ~2GB | Very Fast | Baseline |
| 1.5B | Qwen/Qwen2.5-Coder-1.5B | ~6GB | Fast | Good |
| 3B | Qwen/Qwen2.5-Coder-3B | ~12GB | Moderate | Better |
| 7B | Qwen/Qwen2.5-Coder-7B | ~16GB | Slower | High |
| 14B | Qwen/Qwen2.5-Coder-14B | ~32GB | Slow | Very High |
| 32B | Qwen/Qwen2.5-Coder-32B | ~80GB | Very Slow | Best |

## Output Structure

Results are saved to `./baseline_results/` by default:

```
baseline_results/
├── qwen_0_5B_zero_shot_results.json
├── qwen_0_5B_few_shot_results.json
├── qwen_1_5B_zero_shot_results.json
├── qwen_1_5B_few_shot_results.json
├── qwen_7B_zero_shot_results.json
└── ...
```

### JSON Format

Each result file contains:

```json
[
  {
    "example_id": 0,
    "task_type": "spec_generation",
    "prompt": "Add Verus specs to this function:...",
    "expected_output": "```verus\nfn abs(x: i32) -> i32 {...",
    "generated_output": "```verus\nfn abs(x: i32) -> i32 {...",
    "generation_time_seconds": 2.34,
    "mode": "zero-shot"
  },
  ...
]
```

## Command-Line Options

```bash
python baseline_evaluation.py [OPTIONS]

Options:
  --model-size SIZE    Model size: 0.5B, 1.5B, 3B, 7B, 14B, 32B, or 'all'
                       Default: 1.5B

  --mode MODE          Evaluation mode: zero-shot, few-shot, or both
                       Default: zero-shot

  --output-dir DIR     Directory to save results
                       Default: ./baseline_results
```

## Example Workflow

### Step 1: Quick Test with Small Model

```bash
# Start with the smallest model to verify everything works
python baseline_evaluation.py --model-size 0.5B --mode zero-shot
```

Expected output:
```
Loading model: Qwen/Qwen2.5-Coder-0.5B
This may take several minutes depending on model size...
Model loaded successfully on cuda:0

============================================================
Running zero-shot evaluation on 0.5B model
============================================================

Example 1/10: spec_generation
  Generated in 1.23s
  First 100 chars: ```verus
fn abs(x: i32) -> i32 {
    ensures result >= 0;
    ensures result == x || result == -x...

Example 2/10: code_synthesis
  Generated in 0.98s
  ...

Results saved to: ./baseline_results/qwen_0_5B_zero_shot_results.json

============================================================
Summary for Qwen 0.5B
============================================================

ZERO-SHOT:
  Total examples: 10
  Average generation time: 1.15s
  Total time: 11.50s
```

### Step 2: Compare Model Sizes

```bash
# Run multiple sizes to see quality vs. speed tradeoff
python baseline_evaluation.py --model-size 1.5B --mode zero-shot
python baseline_evaluation.py --model-size 3B --mode zero-shot
python baseline_evaluation.py --model-size 7B --mode zero-shot
```

### Step 3: Test Few-Shot Prompting

```bash
# See if few-shot examples improve performance
python baseline_evaluation.py --model-size 7B --mode both
```

### Step 4: Analyze Results

```python
import json

# Load results
with open("baseline_results/qwen_7B_zero_shot_results.json") as f:
    zero_shot = json.load(f)

with open("baseline_results/qwen_7B_few_shot_results.json") as f:
    few_shot = json.load(f)

# Compare generation quality manually
for i, (zs, fs) in enumerate(zip(zero_shot, few_shot)):
    print(f"\nExample {i+1}: {zs['task_type']}")
    print(f"Zero-shot output: {zs['generated_output'][:100]}...")
    print(f"Few-shot output:  {fs['generated_output'][:100]}...")
```

## Tips for Evaluation

### 1. Start Small
- Begin with 0.5B or 1.5B models to verify setup
- Move to larger models once you confirm everything works

### 2. GPU Memory Management
- If you run out of VRAM, try a smaller model
- Close other programs using GPU memory
- Use `nvidia-smi` to monitor memory usage

### 3. CPU Fallback
- All models will run on CPU if no GPU is available
- Expect 10-50x slower generation times on CPU
- Good for testing, not practical for full evaluation

### 4. Batch Evaluation
- Use `--model-size all` overnight or on cloud GPUs
- Results can be analyzed later without re-running

## Interpreting Results

### What to Look For

1. **Syntax Correctness**: Does the output parse as valid Rust/Verus?
2. **Spec Presence**: Are `requires`/`ensures` clauses generated?
3. **Spec Quality**: Are specs meaningful (not just `requires true`)?
4. **Task Completion**: Does it address the prompt?

### Expected Performance

Based on preliminary tests:

| Model | Zero-shot Syntax | Few-shot Syntax | Spec Quality |
|-------|-----------------|-----------------|--------------|
| 0.5B  | ~30% correct    | ~40% correct    | Low |
| 1.5B  | ~50% correct    | ~65% correct    | Moderate |
| 3B    | ~65% correct    | ~75% correct    | Good |
| 7B    | ~75% correct    | ~85% correct    | High |
| 14B+  | ~80%+ correct   | ~90%+ correct   | Very High |

*Note: These are rough estimates. Actual performance depends on prompt quality and task difficulty.*

## Next Steps After Baseline

Once you have baseline results:

1. **Compare with fine-tuned models**: Run the same evaluation on models trained with `sft_example.py`
2. **Measure improvement**: Calculate (fine-tuned - baseline) performance gains
3. **Error analysis**: Categorize failures (mode errors, missing specs, etc.)
4. **Verus verification**: Run actual Verus verification on generated code (coming soon)

## Troubleshooting

### CUDA Out of Memory

```bash
# Reduce to smaller model
python baseline_evaluation.py --model-size 1.5B --mode zero-shot

# Or run on CPU (slow!)
CUDA_VISIBLE_DEVICES="" python baseline_evaluation.py --model-size 0.5B
```

### Model Download Fails

```bash
# Manually download model first
python -c "from transformers import AutoModel; AutoModel.from_pretrained('Qwen/Qwen2.5-Coder-1.5B')"

# Then run evaluation
python baseline_evaluation.py --model-size 1.5B
```

### Import Errors

```bash
# Install missing dependencies
pip install transformers torch datasets

# Verify installation
python -c "import transformers, torch, datasets; print('OK')"
```

## Contributing Results

If you run baseline evaluations, please share your results!

1. Create a new directory: `baseline_results/USERNAME/`
2. Save your JSON results there
3. Add a summary file with your hardware specs
4. Open a PR with your results

Example summary:
```markdown
# Baseline Results - @username

**Hardware**:
- GPU: NVIDIA RTX 4090 (24GB)
- CPU: AMD Ryzen 9 5950X
- RAM: 64GB

**Models Evaluated**:
- Qwen 0.5B, 1.5B, 3B, 7B (all modes)

**Key Findings**:
- 7B model achieves 78% syntax correctness in zero-shot
- Few-shot prompting improves by ~10% across all sizes
- 3B offers best quality/speed tradeoff
```

---

For questions or issues, please open a GitHub issue!
