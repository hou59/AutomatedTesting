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

public class ALUOtherTest2 {

	@Test(timeout = 4000)
	public void test15() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.leftShift("", 1);
			fail("Expecting exception: StringIndexOutOfBoundsException");
		} catch (StringIndexOutOfBoundsException e) {
		}
	}

	@Test(timeout = 4000)
	public void test16() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.leftShift((String) null, 0);
			fail("Expecting exception: NullPointerException");
		} catch (NullPointerException e) {

		}
	}

	@Test(timeout = 4000)
	public void test49() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.leftShift("f0V", 1);
		assertEquals("0V0", string0);
	}

	@Test(timeout = 4000)
	public void test21() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.ieee754("f", 32);
			fail("Expecting exception: NumberFormatException");
		} catch (NumberFormatException e) {

		}
	}

	@Test(timeout = 4000)
	public void test55() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.ieee754("", 64);
			fail("Expecting exception: StringIndexOutOfBoundsException");
		} catch (StringIndexOutOfBoundsException e) {
		}
	}

	@Test(timeout = 4000)
	public void test56() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.ieee754("", 0);
		assertEquals("", string0);
	}

}
