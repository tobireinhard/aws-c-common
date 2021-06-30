//@ #include "list_ext.gh"

/*@
lemma void mem_after_remove<t>(t m, t r, list<t> ts)
requires m != r &*& mem(m, ts) == true;
ensures mem(m, remove(r, ts)) == true;
{
    switch(ts) {
        case nil:
	case cons(head, tail):
            if (head != m) {
                mem_after_remove(m, r, tail);
            }
    }
}
@*/