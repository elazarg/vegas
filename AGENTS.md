# Agent/LLM Lessons Learned

## General Principles

1. **Run tests continuously during development** - Don't wait until the end to run tests. Use `mvn test -Dtest=SpecificTest` frequently.

2. **Use ASCII-only text** - No unicode characters in code or comments (user preference).

3. **Follow naming conventions consistently**:
   - Use camelCase for variables (e.g., `fieldX`, `actionA`, not `field_x` or `A`)
   - No single-letter or uppercase variable names in tests (e.g., use `alice`/`bob`, not `A`/`B`)

4. **Exception handling**: Check API contracts carefully
   - `ExplicitDag.from()` throws `IllegalArgumentException` on cycles, doesn't return null
   - Wrap in try-catch when null is expected return value

## Project-Specific Knowledge

### Vegas Codebase Structure

- **IR**: `src/main/kotlin/vegas/ir/IR.kt` - Phase-based intermediate representation
- **DAG Infrastructure**: `src/main/kotlin/vegas/dag/` - Generic DAG primitives
- **ActionDag**: `src/main/kotlin/vegas/ir/ActionDag.kt` - Specialized DAG for game actions
- **Typechecker**: `src/main/kotlin/vegas/TypeChecker.kt` - Static analysis
- **Backends**: `src/main/kotlin/vegas/backend/` - Code generation (Solidity, Gambit, SMT)
- **Examples**: `examples/*.vg` - Test games

### Key Technical Details

#### Constraint Placement (Critical Design Principle)

- Constraints on **public values** can be checked when the action happens
- Constraints on **private values** are **obligations** that can only be checked upon reveal
- Example: `yield Host(goat) where Host.goat != Host.car` is WRONG if `Host.car` is hidden
- Correct: `reveal Host(car) where Host.goat != Host.car` - constraint checked when revealed
- See MontyHall.vg for correct structure

#### Reachability

- Use the `Reachability` interface from `vegas.dag` package
- Compute once per DAG using `computeReachability(DagSlice(...))`
- `reach.reaches(u, v)` checks if u can reach v (transitive)
- `reach.comparable(a, b)` checks if either reaches the other (for concurrency testing)

#### Test Environment

- **Java Version**: Project uses Java 25
  - Ensure `JAVA_HOME` is set to your JDK installation (e.g., `export JAVA_HOME=/path/to/jdk-25`)
- **Maven**: Must be available in system PATH
  - If Maven is not in PATH, either add it or use the full path to the `mvn` executable
  - Basic command: `mvn test`
  - Run specific test: `mvn test -Dtest=TestClassName`
  - Quieter output: `mvn -q test`
- **Platform Notes**:
  - On Windows with Git Bash or similar environments, some basic shell commands (grep, tee, tail) may not be available
  - Use Maven's built-in test filtering instead of piping output through shell commands

## Common Issues and Solutions

#### Issue: Tests failing with "Collection should not be empty"
**Cause**: Roles in test don't match actual game roles
**Solution**: Check example .vg files for actual role names (e.g., Prisoners.vg uses "A" and "B", not "Alice" and "Bob")

#### Issue: Visibility validation failing for fields being written
**Cause**: Fields referenced in where clauses were incorrectly treated as reads when they're actually being written in the same action
**Solution**: `val guardReads = sig.requires.captures - writes`
**Rationale**: `yield Host(goat: door) where Host.goat != Guest.d` - the reference to `Host.goat` is a constraint on the value being written, not a read of a prior value

#### Issue: Unsupported IR features causing validation to fail
**Cause**: Some constructs (like let expressions) may not yet be supported in IR lowering
**Solution**: Wrap validation code in try-catch to gracefully handle `IllegalStateException` from `compileToIR()`

#### Issue: Property vs Method confusion
**Cause**: Kotlin properties accessed like methods (e.g., `dag.nodes()` instead of `dag.nodes`)
**Solution**: Check API - if it's a property, access it directly without parentheses

#### Issue: Type inference failures in lambdas
**Cause**: Kotlin can't infer types in complex lambda expressions like `compareBy { ... }`
**Solution**: Use explicit type parameters: `compareBy<ActionId> { ... }`

## Testing Strategy

1. **Test in isolation first**: Use synthetic/minimal test cases without full IR
2. **Then test with real examples**: Use actual .vg example files
3. **Test both valid and invalid cases**: Include negative tests for error conditions
4. **Run related tests together**: Use Maven test patterns like `mvn test -Dtest="Prefix*Test"`
5. **Run continuously during development**: Don't wait until the end to discover test failures

### Golden Master Testing

- **Backend vs Extension Names**: When filtering test cases, ensure `disableBackend` uses backend names, not file extensions
  - Backend names: `"solidity"`, `"solidity-dag"`, `"gambit"`, `"smt"`
  - Extension names: `"sol"`, `"efg"`, `"z3"`
  - Filter by backend name for consistency: `t.backend !in example.disableBackend`
  - Example: `disableBackend=setOf("gambit")` not `setOf("efg")`

### Generated Code Testing

- Test contract structure (verify what's present/absent)
- Test modifiers (verify dependency enforcement)
- Test action functions (verify behavior)
- Don't over-specify output format (e.g., keyword order may vary)
- Test for presence of key elements, not exact syntax

## Backend Implementation Patterns

### Code Reuse

- When building a new backend that needs similar translation logic, make helper functions `internal` instead of `private`
- Examples: `translateType()`, `translateIrExpr()`, `translateWhere()`, `translateDomainGuards()`, `translateAssignments()`
- This allows code reuse without duplication across backends

### Linearization

- When generating code that needs sequential IDs (e.g., Solidity constants), sort nodes deterministically
- Example: `linearizeDag()` sorts by (phase, role name) for determinism
- Maps structured IDs (like ActionId) to simple Ints for use in generated code

### Backend-Specific Requirements

- **Gambit**: Requires enumeration of all possible values to build game tree
  - Cannot handle unbounded types like bare `int` (must be bounded enums)
  - Needs all game states enumerable

- **Solidity**: No enumeration needed
  - Compiles state machine to contract code
  - Can handle unbounded types (e.g., `int256`) directly
  - Focus on dependency tracking and execution flow

## Development Best Practices

1. **Incremental Integration**: When adding major features, use a "strangler fig" pattern:
   - Build new component in isolation with its own tests
   - Integrate into existing system (validation/observation only)
   - Gradually shift usage to new component
   - Remove old component when no longer needed
   - This ensures each step is testable and the system always works

2. **Validation Order**: When multiple validation passes exist:
   - Run cheaper/faster checks first (traditional type checking)
   - Run expensive checks second (IR compilation, DAG validation)
   - Handle unsupported features gracefully (skip validation if IR lowering fails)

3. **Error Messages**: Make validation errors actionable:
   - Include context (which node, what constraint)
   - Point to source location when available
   - Suggest how to fix common issues
