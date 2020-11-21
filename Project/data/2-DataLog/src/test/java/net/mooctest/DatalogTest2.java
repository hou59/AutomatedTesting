package net.mooctest;

import static org.junit.Assert.*;

import org.junit.Test;
import org.junit.Before;
import java.util.LinkedList;

public class DatalogTest2 {

    @Test(expected = NullPointerException.class)
    public void testVariable_0() {
        Variable var = new Variable(null);
    }

    @Test
    public void testVariable() {
        Variable var = new Variable("xavi");
        assertEquals("xavi", var.getIdentifier());
        Variable var2 = new Variable("xavi");
        assertEquals(var2, var);
        if (var == null) {
            assertTrue(true);
        }
        assertNotEquals(null, var);
    }

    @Test
    public void testVariable2() {
        String s = "lel";
        Variable var = new Variable(s);
        assertEquals(s, var.getIdentifier());
        Variable var2 = new Variable(s);
        assertEquals(var2, var);
        if (var == null) assertTrue(true);
        assertNotEquals(null, var);
        assertEquals("VAR:lel", var.toString());
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
}
