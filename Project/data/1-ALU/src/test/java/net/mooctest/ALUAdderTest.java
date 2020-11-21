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

public class ALUAdderTest {

	@Test(timeout = 4000)
	public void test12() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.oneAdder((String) null);
			fail("Expecting exception: NullPointerException");
		} catch (NullPointerException e) {

		}
	}

	@Test(timeout = 4000)
	public void test25() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.claAdder("5szk", (String) null, 'N');
			fail("Expecting exception: NullPointerException");
		} catch (NullPointerException e) {

		}
	}

	@Test(timeout = 4000)
	public void test27() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.adder((String) null, (String) null, 'L', 0);
			fail("Expecting exception: NullPointerException");
		} catch (NullPointerException e) {
		}
	}

	@Test(timeout = 4000)
	public void test28() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.fullAdder('', '', '');
		assertEquals("01", string0);
	}

	@Test(timeout = 4000)
	public void test33() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.claAdder("MK:P", "MK:P", 'k');
		assertEquals("00001", string0);
	}

	@Test(timeout = 4000)
	public void test34() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.claAdder("", "", 'k');
			fail("Expecting exception: StringIndexOutOfBoundsException");
		} catch (StringIndexOutOfBoundsException e) {
		}
	}

	@Test(timeout = 4000)
	public void test35() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.oneAdder("O");
		assertEquals("01", string0);
	}

	@Test(timeout = 4000)
	public void test44() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.adder("}V16;j]}", "I", 's', 5);
		assertEquals("011111", string0);
	}

	@Test(timeout = 4000)
	public void test45() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.adder("I", "r", '2', 9);
		assertEquals("0000000001", string0);
	}

	@Test(timeout = 4000)
	public void test47() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.adder("1", "1", '\"', 2);
			fail("Expecting exception: StringIndexOutOfBoundsException");
		} catch (StringIndexOutOfBoundsException e) {

		}
	}

	@Test(timeout = 4000)
	public void test48() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.oneAdder("");
		assertEquals("1", string0);
	}
}
