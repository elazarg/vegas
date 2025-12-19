package vegas

import vegas.frontend.TypeExp

/**
 * Utility extensions and helper functions for the Vegas compiler.
 */

fun <A, B> Pair<A, A>.map(f: (A) -> B): Pair<B, B> = Pair(f(first), f(second))

/**
 * Shorter alias for joinToString with separator.
 * Provided for conciseness in code generation contexts where joining is frequent.
 */
fun <T> Iterable<T>.join(sep: String) = joinToString(sep)

/**
 * Shorter alias for joinToString with separator and transform function.
 * Provided for conciseness in code generation contexts where joining is frequent.
 */
fun <T> Iterable<T>.join(sep: String, f: (T) -> String) = joinToString(sep) { f(it) }

fun <K, V> Iterable<Map<K, V>>.union(): Map<K, V> = flatMap { xs -> xs.entries.map { it.toPair() } }.toMap()

fun <K> Iterable<Set<K>>.union(): Set<K> = fold(emptySet()) { accumulator, set ->
    accumulator union set
}

// type-specific

fun <T> Iterable<Pair<String, T>>.names() = map { (name, _) -> name }
fun <T> Iterable<Pair<String, T>>.types() = map { (_, type) -> type }

val Pair<String, TypeExp>.name: String get() = first
val Pair<String, TypeExp>.type: TypeExp get() = second
