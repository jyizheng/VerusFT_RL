# Dataset Creation Proposal for VerusSFT

## Goal
Create a high-quality, dependency-clean dataset of self-contained Rust/Verus code snippets—each of which compiles and verifies independently—to support supervised fine-tuning (SFT) and reinforcement learning (RL) for formal verification tasks. Each example will be:

- Tagged as **code**, **spec**, or **proof**
- Validated by Verus for successful or failing verification
- Linked to its source provenance (repo, file path, commit SHA)
- Serialized in a machine-readable format (e.g., JSONL) for use in downstream tasks

This dataset will seed all SFT and RL experiments in VerusSFT and support benchmarking and curriculum design.

## Proposed Methods
We will explore three complementary directions for dataset construction. A robust dataset will likely combine outputs from all three.

### 1. Minimizer-Driven Extraction (Baseline Path)
- **Overview:** Use and extend Verus’s existing minimizer tool (based on `creduce`) to shrink verification programs while preserving successful or failing behavior.
- **Method:**
  - Collect full Verus source files from curated repos (e.g., `verus-lang/verus`, VeriStruct modules, Verismo, etc.).
  - Apply the Verus minimizer with an "interestingness test" (e.g., `verus --verify` with success/failure checks).
  - Wrap output in a standalone crate and validate it compiles/verifies.
  - Label and segment each snippet into exec, spec, and proof zones.
  - Track metadata: origin repo, commit SHA, minimized status, verification result.
- **Strengths:** Leverages existing Verus infrastructure; produces semantically minimal, verification-relevant examples; aligns with RL trajectory mining and failure analysis.
- **Challenges:** Minimization can be slow; some outputs may be over-fragmented or hard to read; might miss human-realistic examples.
- **Status:** Implementation-ready; favored as the first dataset extraction path.

### 2. Program-Slicing + Verus IR-Aware Extraction
- **Overview:** Use static analysis tools (e.g., Flowistry, compiler instrumentation) to slice Rust/Verus programs into smaller, role-tagged units based on control/data dependencies and Verus IR annotations.
- **What Exists:**
  - **Flowistry:** VSCode plugin for Rust program slicing (alpha software, PLDI 2022)
    - Performs backward/forward information flow analysis
    - 94% accuracy on standard Rust codebases
    - **Limitation:** Only works with standard Rust AST/HIR
  - **Verus VIR (Verification Intermediate Representation):**
    - VIR-AST: Internal representation of verifiable Rust subset
    - VIR-SST: Statement-oriented tree for analysis
    - Pipeline: `Rust → HIR → VIR-AST → VIR-SST → AIR → SMT`
- **Method:**
  - Parse AST or intermediate representations (IR) of Verus programs.
  - Identify functions, lemmas, view functions, invariants, etc.
  - Slice programs to retain only the minimal set of dependencies for a particular construct.
  - Use the Verus mode system (exec, ghost, proof) to tag output.
  - Validate that each extracted unit compiles/verifies independently.
- **Strengths:** Produces semantically meaningful slices (e.g., whole lemmas or proofs); avoids over-fragmentation; can track logical dependency graphs for curriculum design.
- **Challenges:**
  - **Flowistry incompatibility:** Flowistry doesn't understand Verus-specific constructs (`ghost` code, `proof` blocks, `spec` functions, `requires`/`ensures`)
  - **High engineering cost:** Would require either (a) forking Flowistry to support Verus (2-4 months), or (b) building custom slicer on VIR (3-6 months)
  - **Unclear benefit:** Minimizer may already produce good results, making this unnecessary
- **Status:** High-reward but experimental; **recommend deferring until Method 1 results are available**. Only pursue if minimizer produces over-fragmented or low-quality outputs.

### 3. AI-Assisted Example Generation and Refinement
- **Overview:** Use a language model (LLM) to propose or refine candidate snippets, with Verus-in-the-loop feedback to ensure dependency-clean, verifiable outputs.
- **Method:**
  - Seed the LLM with code/spec/proof templates from known examples.
  - Prompt the LLM to generate variations, trim dependencies, or repair broken examples.
  - Run Verus verification as feedback; refine or reject based on outcomes.
  - Use the model to suggest human-like completions for partially minimized examples, repair broken code based on error messages, and denoise or simplify multi-function modules.
- **Strengths:** Can generate realistic, semantically rich training examples; useful for hard-to-minimize edge cases (e.g., interactive proof patterns); directly aligned with VerusSFT's long-term RL and agent training goals.
- **Challenges:** Low precision without strong model priors (especially on ghost/view logic); requires verifier-in-the-loop and filtering; may introduce hallucinated or non-compiling artifacts if not constrained.
- **Status:** High-potential augmentation strategy, to be applied selectively after initial dataset bootstrapping.

## Common Requirements Across Methods
- Automate compilation and verification for every snippet to ensure dataset reliability.
- Track provenance (original file paths, commit hashes) for traceability.
- Provide machine-readable labels and metadata to support downstream SFT workflows.

## Scale Targets and Quality Metrics

### Dataset Scale Roadmap

| Phase | Target Size | Method(s) | Timeline Estimate | Status |
|-------|-------------|-----------|-------------------|--------|
| **Current** | 514 examples | Hand-curated IronKV (non-standalone) | - | ✅ Complete |
| **Phase 0** | 514 examples (fixed) | Method 3 (LLM repair of IronKV) | 1.5-2 weeks | 📋 Student Subtask 2 |
| **Phase 1** | 1,000-2,000 | Method 1 (minimizer on 2-3 repos) | 2-4 weeks | 📋 Student Subtask 1 + Scale |
| **Phase 2** | 5,000-10,000 | Method 1 (10+ repos) + Method 3 (augmentation) | 2-3 months | 📋 Planned |
| **Phase 3** | 50,000+ | Method 1 at scale + diversity filters | 6-12 months | 📋 Future |

### Quality Metrics Definition

Each dataset entry should include these quality metrics:

```json
{
  "id": "example_001",
  "code": "...",
  "task": "spec_from_code",
  "metadata": {
    "provenance": {
      "source_repo": "verus-lang/verus",
      "file_path": "source/vstd/vec.rs",
      "commit_sha": "abc123...",
      "extraction_method": "minimizer|manual|llm_repair"
    },
    "verification": {
      "status": "verified|failed|timeout",
      "error_type": "none|precondition|postcondition|invariant|...",
      "verify_time_ms": 1830
    },
    "quality": {
      "self_contained": true,
      "dependencies": ["std", "vstd"],
      "complexity": 7,
      "has_meaningful_spec": true,
      "readability_score": 0.82,
      "minimization_ratio": 0.23
    },
    "labeling": {
      "function_mode": "exec|proof",
      "has_invariant": true,
      "has_proof_block": false,
      "requires_count": 2,
      "ensures_count": 1
    }
  }
}
```

### Acceptance Criteria for Dataset Inclusion

An example is included in the final dataset if it meets ALL of:

1. **Self-contained:** Compiles with only `std`, `core`, or `vstd` dependencies
2. **Verifiable:** Either (a) verifies successfully, OR (b) fails with a recoverable error (for Task C)
3. **Meaningful:** Has at least one `requires`/`ensures` clause OR a loop invariant OR a proof block
4. **Readable:** Quality score ≥ 0.5 (reasonable length, some structure)
5. **Properly labeled:** Can identify exec/spec/proof regions for task construction

### Diversity Requirements

To ensure curriculum design and generalization, the dataset should have:

- **Verification outcome diversity:**
  - 70% verified positive examples
  - 20% repairable errors (pre/post/invariant failures)
  - 10% complex failures (timeout, VC failure)

- **Complexity distribution:**
  - 30% simple (complexity 2-5): single functions, basic specs
  - 50% moderate (complexity 6-15): loops with invariants, multiple specs
  - 20% complex (complexity 16+): proof blocks, nested invariants, ghost code

- **Function mode distribution:**
  - 60-80% `exec` functions (executable code)
  - 20-40% `proof` functions (lemmas and proofs)

- **Source diversity:**
  - Multiple repositories (avoid overfitting to one codebase style)
  - Different verification patterns (data structures, algorithms, systems code)

## Feasibility of Rust/Verus Extraction & Minimization (Subproject 0)

### Context and Objective
The current prototype dataset is small and hand-crafted, limiting diversity and automation. Subproject 0 aims to bootstrap a "minimized, high-quality" corpus of Verus code examples by mining open-source repositories and producing self-contained snippets that compile and verify in isolation. Each snippet will be labeled as executable code, specification, or proof to directly support the broader VerusSFT goal of fine-tuning models on verification-oriented Rust/Verus examples.

### Planned Method and Tools
This subproject leans on existing Verus infrastructure plus lightweight static analysis to automate extraction:

1. **Candidate Discovery:** Scan target repositories for Rust files with Verus verification elements (e.g., `requires`, `ensures`, `proof`). Use simple static analysis (regex or `rg`) to prioritize files dense with verification constructs.
2. **Dependency Isolation:** For each candidate, inspect `use` statements and crate metadata (`cargo metadata`) to ensure only standard library or `vstd` dependencies remain. Inline small intra-repo helpers when needed and skip examples that rely on heavy external crates, keeping each snippet self-contained.
3. **Verus Minimizer Application:** If candidates are still large, run the Verus minimizer (powered by C-Reduce) with an "interestingness" test such as "still verifies" or "still fails with error X" to automatically shrink programs while preserving behavior.
4. **Snippet Assembly & Validation:** Wrap reduced code into a standalone crate or single file, retag exec/spec/proof regions, and re-run Verus to confirm compilation and verification. Record provenance (repo, file path, commit SHA), verification outcome, and whether minimization was applied.

This workflow directly addresses known gaps (tiny dataset, no minimizer integration) and is implementation-ready, providing a concrete path to populate the initial training corpus for downstream multi-task training and evaluation.

---

## Student Subtask: Benchmark and Validate Verus Minimizer for Dataset Generation

### Objective
Validate the feasibility of Method 1 (Minimizer-Driven Extraction) by running a pilot study on the Verus minimizer tool. This will answer critical unknowns about throughput, output quality, and success rate before committing to large-scale dataset generation.

### What Exists
- **Minimizer Location:** [`source/tools/minimizers/`](https://github.com/ChuyueSun/verus/tree/main/source/tools/minimizers) in the Verus repo
- **Available Tools:**
  - `verified_minimal.sh` - most aggressive reduction while preserving verification
  - `verified_with_spec.sh` - preserves specification functions
  - `verified_with_invariant.sh` - keeps invariants
  - Error-focused: `panicked_in.sh`, `rlimit_exceeded.sh`, `time_exceeded.sh`
- **Mechanism:** Uses C-Reduce with custom "interestingness tests"

### Critical Unknowns (To Be Answered)
1. **Throughput:** How long does minimization take per file on representative Verus code?
2. **Output Quality:** Are minimized snippets readable and semantically meaningful, or over-fragmented?
3. **Success Rate:** What percentage of files minimize successfully with zero external dependencies?
4. **Self-containment:** Do minimized outputs compile/verify independently?

### Task Steps

#### Step 1: Sample Selection (1 day)
- Select 20 diverse Rust files from `verus-lang/verus` repository
- Criteria for diversity:
  - Range of sizes: 50-500 LOC
  - Mix of verification complexity (simple functions, complex proofs, loops with invariants)
  - Different file types: examples, tests, library code
- Record original file metadata: path, LOC, verification time

#### Step 2: Minimizer Execution (2-3 days)
- For each of the 20 files, run the minimizer with `verified_minimal.sh`
- Set timeout: 60 minutes per file (abort if exceeds)
- Record for each file:
  - Minimization time (wall clock)
  - Reduction ratio: `minimized_LOC / original_LOC`
  - Success/failure status
  - Any errors encountered

#### Step 3: Quality Assessment (2 days)
For each successfully minimized file:
- **Self-containment check:** Does it compile/verify independently?
  - Run `verus --verify` on minimized output
  - Check dependencies: only `std`, `core`, `vstd` allowed
- **Readability assessment:** Manual review (score 1-5)
  - 5 = readable, semantically meaningful
  - 3 = fragmented but understandable
  - 1 = nonsensical or over-reduced
- **Labeling feasibility:** Can you identify exec/spec/proof regions?

#### Step 4: Analysis and Reporting (1 day)
Create a report with:
- **Throughput metrics:**
  - Average time per file
  - Median reduction ratio
  - Success rate (% of files that minimized successfully)
- **Quality metrics:**
  - Average readability score
  - % self-contained (zero external deps)
  - % verifiable after minimization
- **Recommendations:**
  - Proceed with Method 1? (if >70% success rate, <20 min/file average, readability >3)
  - Suggested optimizations (parallelization, timeout adjustments)
  - Estimated time to generate 1,000 examples

### Deliverables
1. **Benchmark Dataset:** 20 files with original + minimized versions
2. **Metadata Spreadsheet:** Columns: file_path, original_LOC, minimized_LOC, reduction_ratio, minimization_time, success, readability_score, self_contained, verifiable
3. **Written Report:** 2-3 pages with metrics, analysis, and go/no-go recommendation
4. **Code/Scripts:** Any wrapper scripts used to automate minimization and validation

### Success Criteria
- **Green Light (Proceed with Method 1):** >70% success rate, <20 min/file average, >60% readable (score ≥3)
- **Yellow Light (Optimize first):** Slow but high quality → recommend parallelization with 10+ workers
- **Red Light (Reconsider):** <50% success rate or outputs too fragmented → explore Method 2 or 3

### Estimated Timeline
**Total: 1 week (5-7 days)**
- Can be parallelized by running minimizer on multiple files simultaneously

### Prerequisites
- Verus toolchain installed and working (`verus --version`)
- Access to `verus-lang/verus` repository
- Familiarity with bash scripting and C-Reduce basics
- Ability to run computationally intensive tasks (access to multi-core machine recommended)

---

## Student Subtask: Fix and Validate IronKV Dataset with LLM-Assisted Repair

### Objective
The current IronKV dataset (514 examples) was created with a flimsy hacky script and **the examples do not compile or verify independently**. This subtask uses Method 3 (AI-Assisted Repair) to fix these examples and make them standalone, verifiable snippets suitable for training.

### Current State of IronKV Dataset
- **Size:** 514 examples (173 Task A, 159 Task B, 182 Task C after filtering)
- **Format:** JSONL with code snippets and metadata
- **Problem:** Examples were extracted from IronKV codebase but have missing dependencies, incomplete imports, or context dependencies
- **Status:** Examples are structurally correct but not self-contained

### What Needs Fixing
Common issues to expect:
1. Missing `use` statements (e.g., `use vstd::prelude::*`)
2. Missing type definitions or struct declarations
3. Incomplete function signatures (missing generic parameters)
4. Context dependencies (references to other modules not included)
5. Missing `verus!` macro wrapper

### Task Steps

#### Step 1: Validation Baseline (1 day)
- Create a validation script that attempts to compile/verify each example
- For each example in the dataset:
  - Wrap in minimal Cargo project structure
  - Run `verus --verify`
  - Categorize errors: compilation error, verification error, timeout, success
- Record baseline metrics:
  - How many compile successfully? (expected: <10%)
  - How many verify successfully? (expected: <5%)
  - What are the most common error types?

#### Step 2: LLM-Assisted Repair Pipeline (3-4 days)
Build an automated repair pipeline:

```python
for each broken example:
    attempt = 0
    max_attempts = 3

    while attempt < max_attempts and not verifies(example):
        # Extract error message from Verus
        error = run_verus(example)

        # Prompt LLM to fix
        prompt = f"""
        This Verus code snippet doesn't compile/verify:

        {example}

        Error:
        {error}

        Fix the code to make it self-contained and verifiable.
        Only add necessary imports and definitions.
        """

        fixed_example = query_llm(prompt)
        attempt += 1

    if verifies(fixed_example):
        save_to_fixed_dataset(fixed_example)
    else:
        log_unfixable(example, error)
```

**LLM Options to Try:**
- Claude 3.5 Sonnet (best for code repair)
- GPT-4
- Claude Opus (if Sonnet fails)

#### Step 3: Manual Review Sample (1 day)
- Manually review 20-30 LLM-fixed examples
- Check for:
  - **Over-fixing:** Did LLM add too much code or change semantics?
  - **Correctness:** Does the fixed version preserve original intent?
  - **Minimal changes:** Are fixes minimal or did LLM rewrite everything?
- Create quality rubric based on findings

#### Step 4: Full Dataset Repair (2-3 days)
- Run repair pipeline on all 514 examples
- Allow 3 repair iterations per example
- Track metrics:
  - Success rate (% fixed after 1, 2, 3 iterations)
  - Common fix patterns (what did LLM typically add?)
  - Unfixable examples (what are the blockers?)

#### Step 5: Validation and Comparison (1 day)
- Re-run validation on fixed dataset
- Compare before/after:
  - Compilation success rate
  - Verification success rate
  - Average LOC added by LLM
- Create side-by-side diff for 10 representative examples

### Deliverables
1. **Fixed Dataset:** JSONL files with successfully repaired examples
2. **Repair Report:** Metrics on success rate, iteration counts, common fixes
3. **Validation Results:** Before/after comparison showing improvement
4. **Repair Pipeline Code:** Automated script for LLM-assisted repair
5. **Quality Analysis:** Manual review of 20-30 examples with quality scores
6. **Unfixable Examples Log:** List of examples that couldn't be fixed with error analysis

### Success Criteria
- **Strong Success:** >70% of examples compile and verify after LLM repair
- **Moderate Success:** 50-70% success rate; identifies clear patterns for what's fixable
- **Learning Outcome:** <50% success rate but clear understanding of why (informs whether to pursue Method 3 or focus on Method 1)

### Estimated Timeline
**Total: 1.5-2 weeks (8-10 days)**
- Can be partially parallelized (batch LLM queries)

### Prerequisites
- Verus toolchain installed (`verus --version`)
- Access to IronKV dataset (`sft_data/verified-ironkv/`)
- API access to Claude or GPT-4
- Python scripting skills
- Understanding of common Rust/Verus compilation errors

### Expected Outcomes
This subtask will answer:
1. **Is the existing IronKV dataset salvageable?** Or should we start fresh with Method 1?
2. **How effective is LLM-assisted repair for Verus code?** (informs viability of Method 3)
3. **What are common extraction issues to avoid?** (informs future dataset creation)
4. **Can we bootstrap a usable dataset quickly?** (before waiting for Method 1 minimizer results)
