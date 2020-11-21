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

public class ALUFloatTest {

	@Test(timeout = 4000)
	public void test07() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.floatRepresentation("$", 0, 0);
			fail("Expecting exception: NumberFormatException");
		} catch (NumberFormatException e) {

		}
	}

	@Test(timeout = 4000)
	public void test22() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.floatTrueValue((String) null, 0, 0);
			fail("Expecting exception: NullPointerException");
		} catch (NullPointerException e) {

		}
	}

	@Test(timeout = 4000)
	public void test23() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.floatRepresentation("", 0, 0);
			fail("Expecting exception: StringIndexOutOfBoundsException");
		} catch (StringIndexOutOfBoundsException e) {
		}
	}

	@Test(timeout = 4000)
	public void test24() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.floatRepresentation((String) null, 0, 0);
			fail("Expecting exception: NullPointerException");
		} catch (NullPointerException e) {

		}
	}

	@Test(timeout = 4000)
	public void test46() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.floatTrueValue("00000000000000000000000000", 8, 0);
		assertEquals("0.0", string0);
	}

	@Test(timeout = 4000)
	public void test50() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.floatTrueValue("QfVuZ", 4, 2);
			fail("Expecting exception: StringIndexOutOfBoundsException");
		} catch (StringIndexOutOfBoundsException e) {
		}
	}

	@Test(timeout = 4000)
	public void test51() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.floatTrueValue("QfVuZ", 4, 0);
		assertEquals("1.0", string0);
	}

	@Test(timeout = 4000)
	public void test52() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.floatTrueValue("00", 0, 0);
		assertEquals("NaN", string0);
	}

	@Test(timeout = 4000)
	public void test53() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.floatTrueValue("1", 0, 0);
		assertEquals("-Inf", string0);
	}

	@Test(timeout = 4000)
	public void test57() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.floatRepresentation("1", 0, 1);
		assertEquals("NaN", string0);
	}

	@Test(timeout = 4000)
	public void test58() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.floatRepresentation("4.0", 0, 0);
		assertEquals("NaN", string0);
	}

	@Test(timeout = 4000)
	public void test59() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.floatRepresentation("0", 0, 1);
		assertEquals("00", string0);
	}

	@Test(timeout = 4000)
	public void test60() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.floatRepresentation("47", 32, 0);
		assertEquals("010000000000000000000000000000011", string0);
	}
}
