package net.mooctest;

import static org.junit.Assert.*;

import org.junit.Test;
import org.junit.Before;
import java.util.LinkedList;

public class DatalogTest4 {

    Argument x = Argument.value(new Value("xxx"));
    Predicate p = new Predicate("pred");
   
    Datalog d;

    Rule r = new Rule(d, d);
    Program program = new Program(r);
    Fact f = new Fact(p, x.getValue());

    @Test
    public void testProgram() {
        assertArrayEquals(program.getProgram(), new Rule[]{r});
        assertFalse(program.canDerive(f, new Fact[0]));
    }

}
