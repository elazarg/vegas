package vegas

@JvmInline
value class RoleId(val name: String) {
    override fun toString(): String = name
    companion object {
        @JvmStatic fun of(name: String) = RoleId(name)
    }
}

@JvmInline
value class VarId(val name: String) {
    override fun toString(): String = name
    companion object {
        @JvmStatic fun of(name: String) = VarId(name)
    }
}

data class FieldRef(val owner: RoleId, val param: VarId){
    override fun toString(): String = "$owner.$param"
    companion object {
        @JvmStatic fun of(owner: RoleId, param: VarId) = FieldRef(owner, param)
    }
}
