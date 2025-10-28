package vegas.dag

/** LMA: strategic deadlock iff ≥2 distinct owners on the frontier. */
class LmaScheduler<T: Any, C: Any>(
    private val machine: FrontierMachine<T>,
    private val colorOf: (T) -> C
) {
    fun isGraphDeadlocked(): Boolean = !machine.isComplete() && machine.enabled().isEmpty()
    fun isStrategicallyDeadlocked(): Boolean {
        val e = machine.enabled()
        if (e.isEmpty()) return false
        return e.map(colorOf).toSet().size >= 2
    }
    fun enabled(): Set<T> = machine.enabled()
    fun advance(node: T) = machine.resolve(node)
}
