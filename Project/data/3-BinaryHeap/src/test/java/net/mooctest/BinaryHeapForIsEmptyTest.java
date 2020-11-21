package net.mooctest;

import static org.junit.Assert.*;

import org.junit.Test;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.util.Random;

import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;

public class BinaryHeapForIsEmptyTest {

	@Test(timeout=4000)
	public void testforisEmpty() {
		assertTrue(new BinaryHeap().isEmpty());
	}
	
}
