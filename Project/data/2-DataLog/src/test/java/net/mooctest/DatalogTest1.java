package net.mooctest;

import static org.junit.Assert.*;

import org.junit.Test;
import org.junit.Before;
import java.util.LinkedList;

public class DatalogTest1 {

    Predicate p = new Predicate("pred");

    @Test
    public void test() {
        Argument[] a = new Argument[1];
        a[0] = Argument.value(new Value("value"));
        Predicate p = new Predicate("pre");
        Datalog f = new Datalog(p, a);
        assertArrayEquals(a, f.getArguments());
    }

    @Test
    public void testDatalogGets() {
        Predicate pred = new Predicate("testing");
        Value val = new Value("42");
        Argument arg = Argument.value(val);
        Datalog test = new Datalog(pred, arg);

        Predicate returned = test.getPredicate();
        assertEquals(pred, returned);
    }

    @Test
    public void testDatalogSames() {
        Predicate pred = new Predicate("testing");
        Value val = new Value("42");
        Argument arg = Argument.value(val);
        Datalog test = new Datalog(pred, arg);
        Datalog test2 = new Datalog(pred, arg);

        assertEquals(test2, test);
    }

    @Test
    public void testDatalog2() {
        Predicate p = new Predicate("pres");

        Argument[] a = new Argument[2];
        a[0] = Argument.value(new Value("values"));
        a[1] = Argument.variable(new Variable("variables"));

        Datalog f = new Datalog(p, a);

        assertEquals("pres(values,VAR:variables)", f.toString());
    }

}
