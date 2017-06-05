import XCTest
import LogicKit
@testable import heidi

struct Wrapper : Equatable, CustomStringConvertible {
  let term : Term

  var description: String {
      return "\(self.term)"
  }

  static func ==(lhs: Wrapper, rhs: Wrapper) -> Bool {
    return (lhs.term).equals (rhs.term)
  }

}

func resultsOf (goal: Goal, variables: [Variable]) -> [[Variable: Wrapper]] {
    var result = [[Variable: Wrapper]] ()
    for s in solve (goal) {
        let solution  = s.reified ()
        var subresult = [Variable: Wrapper] ()
        for v in variables {
            subresult [v] = Wrapper (term: solution [v])
        }
        if !result.contains (where: { x in x == subresult }) {
            result.append (subresult)
        }
    }
    return result
}

class heidiTests: XCTestCase {

// -------- Syntax Tests --------
//For the syntax we are going to test one of each for the sake of time, space and legibility.
//The rest follows he same sructure.

    // Heidi
    func testPlaunHT(){
      let V = Variable(named: "V")
      let goal = HT_Plaun(plaun, V, List.empty)
      let expected = List.cons(hee, List.cons(hee, List.cons(hee, List.cons(hee, List.cons(pause, List.empty)))))

      XCTAssert(goal.equals(expected), "command is incorrect")
    }

    //Tita
    func testDretgTH(){
      let V = Variable(named: "V")
      let goal = TH_Dretg(dretg, V, List.empty)
      let expected = List.cons(whee, List.cons(who, List.cons(pause, List.empty)))

      XCTAssert(goal.equals(expected), "whistle command is incorrect")
    }

// -------- Semantics Tests --------
/*
    //Heidi
    func testTranslateHT(){
      let V = Variable(named: "V")

      var from = List.cons(dretg, List.cons(deponer, List.cons(saFermar, List.cons(returnar, List.empty))))
      var to = Translate_HT(from, V)
      var expected = List.cons(whee, List.cons(who, List.cons(pause, List.cons(short, List.cons(short, List.cons(pause, List.cons(long, List.cons(pause, List.cons(whee, List.cons(whee, List.cons(wheet, List.cons(pause, List.empty))))))))))))

      XCTAssertEqual(resultsOf(goal: to, variables: [V]), expected, "command translation is false")
    }

    //Tita
    func testTranslateTH(){
      let V = Variable(named: "V")

      var from = List.cons(whee, List.cons(who, List.cons(pause, List.cons(short, List.cons(short, List.cons(pause, List.cons(long, List.cons(pause, List.cons(whee, List.cons(whee, List.cons(wheet, List.cons(pause, List.empty))))))))))))
      var to = Translate_TH(from, V)
      var expected = List.cons(dretg, List.cons(deponer, List.cons(saFermar, List.cons(returnar, List.empty))))

      XCTAssertEqual(resultsOf(goal: to, variables: [V]), expected, "whistle command translation is false")
    }
*/
    //Translation -- what ever the command you give either in romansh or whistle it translates
    func testTranslate(){
      let V = Variable(named: "V")

      var fromHeidi = List.cons(dretg, List.cons(deponer, List.cons(saFermar, List.cons(returnar, List.empty))))
      var toTita = Translate(fromHeidi, V)
      var expectedHT = List.cons(whee, List.cons(who, List.cons(pause, List.cons(short, List.cons(short, List.cons(pause, List.cons(long, List.cons(pause, List.cons(whee, List.cons(whee, List.cons(wheet, List.cons(pause, List.empty))))))))))))

      XCTAssertEqual(resultsOf(goal: toTita, variables: [V]), expectedHT, "command-whistle translation is inaccurate")

      var fromTita = List.cons(whee, List.cons(who, List.cons(pause, List.cons(short, List.cons(short, List.cons(pause, List.cons(long, List.cons(pause, List.cons(whee, List.cons(whee, List.cons(wheet, List.cons(pause, List.empty))))))))))))
      var toHeidi = Translate(fromTita, V)
      var expectedTH = List.cons(dretg, List.cons(deponer, List.cons(saFermar, List.cons(returnar, List.empty))))

      XCTAssertEqual(resultsOf(goal: toHeidi, variables: [V]), expectedTH, "whistle-command translation is inaccurate")
    }
//----------------------------------

// -------- Optimized Tests --------

// -------- Syntax Tests --------
//For the syntax we are going to test one of each for the sake of time, space and legibility.
//The rest follows he same sructure.

    // Heidi
    func testPlaunHTopt(){
      let V = Variable(named: "V")
      let goal = HT_Plaun_opt(plaun, V, List.empty)
      let expected = List.cons(wheet, List.cons(wheeo, List.cons(wheet, List.cons(pause, other))))

      XCTAssert(goal.equals(expected), "command is incorrect")
    }

    //Tita
    func testDretgTHopt(){
      let V = Variable(named: "V")
      let goal = TH_Dretg_opt(dretg, V, List.empty)
      let expected = List.cons(hee, List.cons(wheet, List.cons(pause, other)))

      XCTAssert(goal.equals(expected), "whistle command is incorrect")
    }

// -------- Semantics Tests --------
/*
    //Heidi
    func testTranslateHTopt(){
      let V = Variable(named: "V")

      var from = List.cons(dretg, List.cons(deponer, List.cons(saFermar, List.cons(returnar, List.empty))))
      var to = Translate_HT_opt(from, V)
      var expected = List.cons(dretg, List.cons(deponer, List.cons(saFermar, List.cons(returnar, List.empty))))

      XCTAssertEqual(resultsOf(goal: to, variables: [V]), expected, "command translation is false")
    }

    //Tita
    func testTranslateTHopt(){
      let V = Variable(named: "V")

      var from = List.cons(dretg, List.cons(deponer, List.cons(saFermar, List.cons(returnar, List.empty))))
      var to = Translate_TH_opt(from, V)
      var expected = List.cons(dretg, List.cons(deponer, List.cons(saFermar, List.cons(returnar, List.empty))))

      XCTAssertEqual(resultsOf(goal: to, variables: [V]), expected, "whistle command translation is false")
    }
*/

    func testTranslateOPT(){
      let V = Variable(named: "V")

      var fromHeidi = List.cons(dretg, List.cons(deponer, List.cons(saFermar, List.cons(returnar, List.empty))))
      var toTita = Translate_opt(fromHeidi, V)
      var expectedHT = List.cons(hee, List.cons(wheet, List.cons(pause, List.cons(wheeo, List.cons(hee, List.cons(wheet, List.cons(pause, List.cons(wheeo, List.cons(wheeo, List.cons(pause, List.cons(wheeo, List.cons(wheet, List.cons(pause, List.empty)))))))))))))

      XCTAssertEqual(resultsOf(goal: toTita, variables: [V]), expectedHT, "optimized command-whistle translation is inaccurate")

      var fromTita = List.cons(hee, List.cons(wheet, List.cons(pause, List.cons(wheeo, List.cons(hee, List.cons(wheet, List.cons(pause, List.cons(wheeo, List.cons(wheeo, List.cons(pause, List.cons(wheeo, List.cons(wheet, List.cons(pause, List.empty)))))))))))))
      var toHeidi = Translate_opt(fromTita, V)
      var expectedTH = List.cons(dretg, List.cons(deponer, List.cons(saFermar, List.cons(returnar, List.empty))))

      XCTAssertEqual(resultsOf(goal: toHeidi, variables: [V]), expectedTH, "optimized whistle-command translation is inaccurate")
    }
//----------------------------------

// -------- Accelerated Tests --------


//----------------------------------

    static var allTests : [(String, (heidiTests) -> () throws -> Void)] {
        return [
            ("testPlaunHT", testPlaunHT),
            ("testDretgTH", testDretgTH),
            ("testTranslate", testTranslate),
            ("testPlaunHTopt", testPlaunHTopt),
            ("testDretgTHopt", testDretgTHopt),
            ("testTranslateOPT", testTranslateOPT),
        ]
    }
}
