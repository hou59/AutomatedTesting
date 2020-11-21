package net.mooctest;

import static org.junit.Assert.*;

import org.junit.Test;
import org.junit.Before;
import java.util.LinkedList;

public class DatalogTest3 {
   
    @Test
    public void testFact() {
        Predicate p = new Predicate("pre");
        Value[] v = new Value[2];
        v[0] = new Value("value");
        v[1] = new Value("value2");
        Fact x = new Fact(p, v);
        assertEquals("pre(value,value2)", x.toString());
        Fact ff = new Fact(p, v);
        assertFalse(ff.equals(null));
        assertFalse(ff.equals(new Fact(p, new Value("asdasdsd"))));
        assertTrue(ff.equals(new Fact(p, v)));
        assertFalse(ff.equals(new String("idVar")));
    }



}
