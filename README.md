# Vegas: A Domain-Specific Language for Game-Theoretically Analyzed Blockchain-Based Games

Vegas (VErified Game Analysis and Synthesis) is a research tool that provides a unified language for specifying multi-party games with economic incentives. It compiles a single game specification into both **game-theoretic models** (for analysis) and **smart contracts** (for deployment), ensuring the implementation faithfully preserves the game's strategic properties.

## Overview

Vegas allows you to specify strategic interactions between multiple parties, including:
- Players joining with deposits
- Sequential and simultaneous moves
- Hidden information and reveal mechanisms
- Conditional payouts based on game outcomes

The compiler uses a **Dependency DAG (Directed Acyclic Graph)** approach to schedule actions. Unlike traditional round-based systems, Vegas allows actions to occur asynchronously as soon as their dependencies (data or control flow) are met.

From a single Vegas specification, the tool generates:
- **Solidity Smart Contracts**: Optimized, asynchronous contracts with automatic timeout handling.
- **Extensive Form Games**: Gambit (`.efg`) files for finding Nash equilibria and analyzing strategy.

## Language Features

### Core Constructs

- **Declarative Flow**: Define actions (`yield`, `reveal`) naturally; the compiler infers the necessary execution order.
- **Macros**: Define reusable logic and predicates to keep specifications clean.
- **Automatic Commit-Reveal**: The compiler automatically detects concurrent public moves that are vulnerable to front-running and rewrites them into secure commit-reveal protocols.
- **Distribution Transparency**: Write code as if it were a centralized sequential game. The compiler handles the complexity of distributed state, cryptographic commitments, and timeouts.

### Example: Monty Hall Game

```vegas
type door = {0, 1, 2}

// Players join with deposits
join Host() $ 100;
join Guest() $ 100;

// Host hides the car (compiler generates commitment)
yield Host(car: hidden door);

// Guest makes a public choice
yield Guest(d: door);

// Host reveals a goat (constrained by game rules)
yield Host(goat: door) where Host.goat != Guest.d;

// Guest decides whether to switch
yield Guest(switch: bool);

// Host reveals the car's location
reveal Host(car: door) where Host.goat != Host.car;

// Payouts calculated based on game state
withdraw (Host.car != null && Guest.switch != null)
     ? { Guest -> ((Guest.d != Host.car) <-> Guest.switch) ? 20 : -20;  Host -> 0 }
     : (Host.car == null)
     ? { Guest -> 20;   Host -> -100 } // Host timed out/bailed
     : { Guest -> -100; Host -> 0 }    // Guest timed out/bailed
````

## Building and Running

### Build

```bash
# Generate ANTLR parser
antlr4 -o ./generated/vegasGen -package vegasGen -listener -visitor -lib . ./Vegas.g4

# Compile Kotlin code
kotlinc src/vegas/*.kt -cp antlr-runtime.jar
```

### Run

```bash
kotlin -cp .:antlr-runtime.jar vegas.MainKt
```

This will process example files and generate outputs in:

  - `examples/gambit/` - Extensive form game files (.efg)
  - `examples/solidity/` - Smart contract implementations (.sol)
  - `examples/graphviz/` - Visualizations of the action dependency DAG

## Output Formats

### Solidity Smart Contracts

Generates Ethereum smart contracts that implement:

  - **DAG-Based Scheduling**: Actions are gated by `depends` modifiers, allowing non-conflicting actions to occur in any order.
  - **Bail-Out Logic**: If a player stops responding, they are marked as "bailed" after a timeout. Dependent actions can then proceed (treating the missing values as `null`), preventing the game from freezing permanently.
  - **Cryptographic Security**: Commitments and reveals are generated automatically for hidden information and "risk partners" (concurrent moves).

### Gambit EFG

Generates extensive form game representations that map the DAG structure to information sets, correctly modeling:

  - **Simultaneity**: Actions that can execute concurrently in the DAG are modeled as simultaneous moves in the game tree.
  - **Information Sets**: Players only "know" information that has been explicitly revealed or is public in the DAG history.
