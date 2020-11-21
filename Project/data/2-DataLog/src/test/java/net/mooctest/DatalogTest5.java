package net.mooctest;

import static org.junit.Assert.*;

import org.junit.Test;
import org.junit.Before;
import java.util.LinkedList;

public class DatalogTest5 {

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

    @Test(expected = NullPointerException.class)
    public void blow1() {
        assertFalse(program.canDerive(f, new Fact[]{f}));
    }

    @Test(expected = NullPointerException.class)
    public void blowTestPredicate() {
        new Predicate(null);
    }

    @Test(expected = NullPointerException.class)
    public void blowTestValue() {
        new Value(null);
    }

    @Test(expected = NullPointerException.class)
    public void blowTestFact() {
        new Fact(null);
    }

    @Test(expected = NullPointerException.class)
    public void blowTestFact2() {
        new Fact(p, null);
    }


}
