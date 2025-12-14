package vegas

import vegas.frontend.parseFile
import vegas.frontend.compileToIR
import vegas.backend.move.MoveRenderer
import vegas.backend.move.compileToMove
import vegas.backend.move.SuiPlatform
import java.io.File

fun updateGoldenMasters() {
    val exampleFiles = listOf(
        "Bet", "MontyHall", "MontyHallChance", "OddsEvens", "OddsEvensShort",
        "Prisoners", "Simple", "Trivial1", "Puzzle", "ThreeWayLottery",
        "ThreeWayLotteryBuggy", "ThreeWayLotteryShort", "TicTacToe"
    )

    exampleFiles.forEach { example ->
        try {
            val prog = parseFile("examples/$example.vg").copy(name = example, desc = example)
            val ir = compileToIR(prog)
            val output = MoveRenderer().render(compileToMove(ir, SuiPlatform))

            val file = File("examples/move/$example.move")
            file.writeText(output)
            println("Updated $example.move")
        } catch (e: Exception) {
            println("Skipped $example: ${e.message}")
        }
    }
}

// Main entry point to run this as a script
fun main() {
    updateGoldenMasters()
}
