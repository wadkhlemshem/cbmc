package com.diffblue.java_testcase;

import org.mockito.stubbing.Answer;
import org.mockito.invocation.InvocationOnMock;
import java.util.ArrayList;

public class IterAnswer<T> implements Answer<T> {

    private int idx = 0;
    private ArrayList<T> answers;

    public IterAnswer(ArrayList<T> _answers) {
	answers = _answers;
    }
    
    public T answer(InvocationOnMock invocation) {
	return answers.get(idx++);
    }    

}

