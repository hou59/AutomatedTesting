package net.mooctest;

import static org.junit.Assert.*;

import org.junit.Test;
import org.junit.Before;
import java.util.LinkedList;

public class DatalogOtherTest {
    
    Argument x = Argument.value(new Value("xxx"));
    Predicate p = new Predicate("pred");
   
    Datalog d;

    Rule r = new Rule(d, d);
    Program program = new Program(r);
    Fact f = new Fact(p, x.getValue());

    @Before
    public void initialize() {
        d = new Datalog(p, x);
    }

    @Test
    public void testRule() {
        r = new Rule(d, d);
        assertEquals(r.getHead(), d);
        assertArrayEquals(r.getBody(), new Datalog[]{d});
        assertEquals("pred(xxx) :- pred(xxx).", r.toString());
    }

    @Test
    public void testSubstitution() {
        LinkedList ll = new LinkedList<Variable>();
        ll.add(x);
        Substitution s = new Substitution();
        s.extend(new Variable("asd"), x.getValue());
        s.extend(new Variable("asd"), new Value("adofjsdfn"));
        LinkedList lls = new LinkedList<Substitution>();
        s.extendAll(lls);
        assertEquals(d.getPredicate(), s.applyOn(d).getPredicate());
    }

    @Test
    public void testVariable3() {
        Variable v = new Variable("idVar");
        assertFalse(v.equals(null));
        assertFalse(v.equals(new Variable("ads")));
        assertTrue(v.equals(new Variable("idVar")));
        assertFalse(v.equals(new String("idVar")));
        assertEquals(v.hashCode(), v.hashCode());
    }

    @Test
    public void testValue() {
        Value v = new Value("idVar");
        assertEquals(v.getValue(), v.toString());
        assertEquals(v.getValue(), "idVar");
        assertFalse(v.equals(null));
        assertFalse(v.equals(new Value("ads")));
        assertTrue(v.equals(new Value("idVar")));
        assertFalse(v.equals(new String("idVar")));
        assertEquals(v.hashCode(), v.hashCode());

    }

    @Test
    public void testPredicate() {
        Predicate v = new Predicate("idVar");
        assertEquals(v.getName(), v.toString());
        assertEquals(v.getName(), "idVar");
        assertFalse(v.equals(null));
        assertFalse(v.equals(new Predicate("ads")));
        assertTrue(v.equals(new Predicate("idVar")));
        assertFalse(v.equals(new String("idVar")));
        assertEquals(v.hashCode(), v.hashCode());
    }
}
