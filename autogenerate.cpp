#include <iostream>

using namespace std;

int main() {
    /*for (int i = 31; i <= 40; i++) {
        cout << "Definition hash_" << i << "_correct_def (ll: LedgerLRecord rec) : Prop." << endl;
        cout << "execs0 (hash_" << i << " rec def) :" << endl;
        cout << "ll | \"m_string\" \"m_modulo\" \"m_multiplier\" -> l1 | \"m_hash\"." << endl;
        cout << "con (m_hash = fst (reference_hash_implementation " << i << "%nat m_string (uint2N m_multiplier) (uint2N m_modulo)))." << endl;
        cout << "Defined." << endl;
        cout << endl;
    }*/

    string s;
    cin >> s;
    for (int i = 1; i <= 40; i++) {
        /*cout << "find . -type f -name \"*.v\" -print0 | xargs -0 sed -i \"s/";
        for (int j = 1; j < i; j++) {
            cout << "@hash_" << j;
        }
        cout << "/";
        for (int j = i - 1; j >= 1; j--) {
            cout << "@hash_" << j << " ";
        }
        cout << "/g\"" << endl;*/

        cout << "Lemma hash_" << i << "_prf (ll : LedgerLRecord rec) : hash_" << i << "_correct_def ll." << endl;
        cout << "start_proof; hash_" << i << "_start." << endl;
        cout << "continue_all_custom ";
        for (int j = i - 1; j >= 1; j--) {
            cout << "@hash_" << j << " ";
        }
        cout << "." << endl;
        cout << "prepare ll P loc_." << endl;
        cout << "time \"[simple][" << s << "][" << i << "]\" timeout 300 solver." << endl;
        cout << "Time Qed." << endl;
        cout << endl;

        /*cout << "#[returns=ret_]" << endl;
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
        cout << endl;*/

        /*cout << "Ursus Definition hash_" << i << ": UExpression PhantomType false." << endl;
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
        cout << endl;*/
    }
}