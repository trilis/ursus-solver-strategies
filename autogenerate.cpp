#include <iostream>

using namespace std;

int main() {
    for (int i = 11; i <= 30; i++) {
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
    }
}