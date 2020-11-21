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

public class ALUGateTest {

	@Test(timeout = 4000)
	public void test29() throws Throwable {
		ALU aLU0 = new ALU();
		char char0 = aLU0.xorGate('S', 'S');
		assertEquals('0', char0);
	}

	@Test(timeout = 4000)
	public void test30() throws Throwable {
		ALU aLU0 = new ALU();
		char char0 = aLU0.xorGate('=', 'C');
		assertEquals('1', char0);
	}

	@Test(timeout = 4000)
	public void test31() throws Throwable {
		ALU aLU0 = new ALU();
		char char0 = aLU0.andGate('N', 'N');
		assertEquals('0', char0);
	}

	@Test(timeout = 4000)
	public void test32() throws Throwable {
		ALU aLU0 = new ALU();
		char char0 = aLU0.andGate('1', '8');
		assertEquals('0', char0);
	}
}
