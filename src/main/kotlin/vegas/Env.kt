package vegas


data class Env<T>(val g: Map<VarId, T>, val r: Map<RoleId, T>, val h: Map<FieldRef, T>) {
    constructor(): this(mapOf(), mapOf(), mapOf())

    operator fun plus(p: Pair<VarId, T>) = Env(g + p, r, h)
    operator fun plus(p: Map<VarId, T>) = Env(g + p, r, h)
    infix fun withMap(p: Map<FieldRef, T>) = Env(g, r, h + p)

    fun getValue(role: RoleId, field: VarId) = getValue(FieldRef(role, field))
    fun getValue(m: FieldRef) = h.getValue(m)

    fun getValue(v: VarId) = g.getValue(v)
    fun getValue(role: RoleId) = r.getValue(role)

    // Utils
    val Pair<RoleId, VarId>.role: RoleId get() = first
    val Pair<RoleId, VarId>.field: VarId get() = second
}
