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

public class ALUIntegerTest {

	@Test(timeout = 4000)
	public void test01() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.integerSubtraction("", "", (-1));
			fail("Expecting exception: StringIndexOutOfBoundsException");
		} catch (StringIndexOutOfBoundsException e) {

		}
	}

	@Test(timeout = 4000)
	public void test08() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.integerRepresentation("+", 0);
			fail("Expecting exception: NumberFormatException");
		} catch (NumberFormatException e) {

		}
	}

	@Test(timeout = 4000)
	public void test17() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.integerTrueValue((String) null);
			fail("Expecting exception: NullPointerException");
		} catch (NullPointerException e) {

		}
	}


	@Test(timeout = 4000)
	public void test19() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.integerRepresentation("", 0);
			fail("Expecting exception: StringIndexOutOfBoundsException");
		} catch (StringIndexOutOfBoundsException e) {
		}
	}

	@Test(timeout = 4000)
	public void test20() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.integerRepresentation((String) null, 0);
			fail("Expecting exception: NullPointerException");
		} catch (NullPointerException e) {

		}
	}

	@Test(timeout = 4000)
	public void test37() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.integerRepresentation("0", 1);
		assertEquals("0", string0);
	}

	@Test(timeout = 4000)
	public void test38() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.integerRepresentation("1", 0);
		assertEquals("1", string0);
	}

	@Test(timeout = 4000)
	public void test39() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.integerRepresentation("0", 0);
		assertEquals("", string0);
	}

	@Test(timeout = 4000)
	public void test40() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.integerRepresentation("-", 0);
			fail("Expecting exception: NumberFormatException");
		} catch (NumberFormatException e) {

		}
	}

	@Test(timeout = 4000)
	public void test54() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.integerTrueValue("gz");
		assertEquals("-36", string0);
	}

	@Test(timeout = 4000)
	public void test61() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.integerSubtraction((String) null, (String) null, 0);
			fail("Expecting exception: NullPointerException");
		} catch (NullPointerException e) {

		}
	}
}
