package net.mooctest;

import static org.junit.Assert.*;

import org.junit.Test;
import org.junit.Before;
import java.util.LinkedList;

public class DatalogTest {


    Argument x = Argument.value(new Value("xxx"));
    Predicate p = new Predicate("pred");
   
    Datalog d;


    @Before
    public void initialize() {
        d = new Datalog(p, x);
    }

    @Test(expected = NullPointerException.class)
    public void blowConstructor1() {
        new Datalog(null, x);
    }

    @Test(expected = NullPointerException.class)
    public void blowConstructor2() {
        new Datalog(p, null);
    }

    @Test
    public void getPredicate() throws Exception {
        assertEquals(p, d.getPredicate());
    }

    @Test
    public void getArguments() throws Exception {
        assertArrayEquals(d.getArguments(), new Argument[]{x});
    }

    @Test
    public void equals() throws Exception {
        assertFalse(d.equals(null));
        Datalog other = new Datalog(p, new Argument[0]);
        assertFalse(d.equals(other));
        assertFalse(d.equals(new String("")));
        assertTrue(d.equals(d));
    }


    @Test
    public void hashCodeTest() throws Exception {
        assertEquals(d.hashCode(), d.hashCode());
        Datalog other = new Datalog(p, new Argument[0]);
        assertEquals(other.hashCode(), other.hashCode());
    }

    @Test
    public void substituteTo() throws Exception {
        assertTrue(d.compatibleWith(new Fact(p, x.getValue())));
        assertFalse(d.compatibleWith(new Fact(new Predicate("adsd"), x.getValue())));
        assertFalse(d.compatibleWith(new Fact(new Predicate("adsd"), new Value[0])));
    }

    @Test
    public void toFact() throws Exception {
        assertEquals(d.toFact(), new Fact(p, x.getValue()));
        Datalog other = new Datalog(p, new Argument[0]);
        assertEquals(d.toFact(), new Fact(p, x.getValue()));
        assertEquals(x.getVariable(), x.getVariable());
        assertEquals(x.getVariable(), x.getVariable());
    }


}
