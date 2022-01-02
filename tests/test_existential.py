from pyswip import Prolog
import prolexa.meta_grammar as meta
import nltk
nltk.download('omw-1.4')

# init
pl = Prolog()
meta.reset_grammar()
meta.initialise_prolexa(pl)

def ask(input):
    return meta.standardised_query(pl, input)[0]['Output']

def test_add_rule():
    ans = ask('some humans are teachers')
    ans = ask('are some humans teachers')
    assert ans == b'some humans are teachers'
#
def test_exist_rule():
    ans = ask('some humans are teachers')
    ans = ask('every human is mortal')
    ans = ask('are some teachers mortal')
    assert ans == b'some teachers are mortal'
