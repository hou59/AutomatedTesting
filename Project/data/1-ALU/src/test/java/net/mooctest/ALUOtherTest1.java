package net.mooctest;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.util.Random;

import org.junit.Test;

public class ALUOtherTest1 {

	@Test(timeout = 4000)
	public void test13() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.normalize((String) null);
			fail("Expecting exception: NullPointerException");
		} catch (NullPointerException e) {

		}
	}

	@Test(timeout = 4000)
	public void test14() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.negation((String) null);
			fail("Expecting exception: NullPointerException");
		} catch (NullPointerException e) {

		}
	}

	@Test(timeout = 4000)
	public void test36() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.negation("0");
		assertEquals("1", string0);
	}

	@Test(timeout = 4000)
	public void test41() throws Throwable {
		ALU aLU0 = new ALU();
		int int0 = aLU0.normalize("0");
		assertEquals(1, int0);
	}

	@Test(timeout = 4000)
	public void test42() throws Throwable {
		ALU aLU0 = new ALU();
		int int0 = aLU0.normalize("");
		assertEquals(0, int0);
	}

	@Test(timeout = 4000)
	public void test43() throws Throwable {
		ALU aLU0 = new ALU();
		int int0 = aLU0.normalize("g");
		assertEquals(1, int0);
	}
}
