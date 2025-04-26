#include <iostream>

using namespace std;

int main() {
    for (int i = 1; i <= 30; i++) {
        cout << "Definition hash_" << i << "_correct_def (ll: LedgerLRecord rec) : Prop." << endl;
        cout << "execs0 (hash_" << i << " rec def) :" << endl;
        cout << "ll | \"m_string\" \"m_modulo\" \"m_multiplier\" -> l1 | \"m_hash\"." << endl;
        cout << "con (m_hash = fst (reference_hash_implementation " << i << "%nat m_string (uint2N m_multiplier) (uint2N m_modulo)))." << endl;
        cout << "Defined." << endl;
        cout << endl;
    }

    /*for (int i = 11; i <= 30; i++) {
        cout << "#[returns=ret_]" << endl;
        cout << "Ursus Definition hash_" << i << ": UExpression (uint64 * uint64) false." << endl;
        cout << "{" << endl;
        cout << "    ::// [m_current_power, m_hash] := hash_" << i - 1 << "()." << endl;
        cout << "    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo." << endl;
        cout << "    ::// m_hash := (m_hash + m_string[[{" << i - 1 << "}]] * m_current_power) % m_modulo." << endl;
        cout << "    ::// ret_ := [m_current_power, m_hash] |." << endl;
        cout << "}" << endl;
        cout << "return." << endl;
        cout << "Defined." << endl;
        cout << "Sync." << endl;
        cout << endl;

        cout << "Ursus Definition hash_" << i << ": UExpression PhantomType false." << endl;
        cout << "{" << endl;
        cout << "    ::// var00 current_power: uint64 := {1} ;_|." << endl; 
        cout << "    ::// m_hash := {0} ;_|." << endl;
        for (int j = 0; j < i; j++) {
            if (j % 2 == 0) {
                cout << "    |-----------------------------." << endl;
            }
            if (j != i - 1) {
                cout << "    ::// m_hash := (m_hash + m_string[[{" << j << "}]] * current_power) % m_modulo." << endl;
                cout << "    ::// current_power := (current_power * m_multiplier) % m_modulo." << endl;
            } else {
                cout << "    ::// m_hash := (m_hash + m_string[[{" << j << "}]] * current_power) % m_modulo |." << endl;
            }
        }
        cout << "}" << endl;
        cout << "return." << endl;
        cout << "Defined." << endl;
        cout << "Sync." << endl;
        cout << endl;
    }*/
}