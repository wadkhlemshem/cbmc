package com.diffblue.java_testcase;

import org.objenesis.Objenesis;
import org.objenesis.ObjenesisStd;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;

/**
 * Describe class <code>Reflector</code> here.
 *
 * @author Matthias Guedemann
 * @version 1.0
 */
public class Reflector
{

  /**
   * Changes a given field of an object instance via reflection, bypassing the
   * private modifier.
   *
   * @param o an <code>Object</code> instance to change
   * @param fieldName a <code>String</code> the name of the field to change
   * @param newVal an <code>Object</code> the new value for the field
   */
  public void setInstanceField(Object o, String fieldName, Object newVal)
  {
    Field f;

    try
    {
      f = o.getClass().getField(fieldName);
    }
    catch (NoSuchFieldException nsf)
    {
      // field is not public
      try
      {
        f = o.getClass().getDeclaredField(fieldName);
      }
      catch (NoSuchFieldException nsf2)
      {
        // Field does not exist -> do nothing
	  System.out.println("Field not found");  
        return;
      }
    }

    try
    {
    	f.setAccessible(true);
    	f.set(o, newVal);
    }
    catch (IllegalAccessException ie)
    {
    	System.out.println("ERROR: illegal access, field " + fieldName +
    			" cannot be set");
    	System.out.println(ie);
    }
  }

  /**
   * This forces the creation of an instance for a given class name.
   *
   * @param className a <code>String</code> giving the name of the class
   * @return an <code>Object</code> which is an instance of the specified class
   * @exception ClassNotFoundException if the class cannot be found in the
   * classpath
   */
  public Object forceInstance(String className) throws ClassNotFoundException
  {
    Class c = Class.forName(className);
    return forceInstance(c);
  }

  private boolean hasDefaultConstructor(Class c)
  {
    for(Constructor ctor : c.getConstructors())
      if (ctor.getParameterTypes().length == 0)
        return true;

    return false;
  }

  private boolean hasDefaultPrivateConstructor(Class c)
  {
    for(Constructor ctor : c.getDeclaredConstructors())
      if (ctor.getParameterTypes().length == 0)
      {
        ctor.setAccessible(true);
        return true;
      }

    return false;
  }

  /**
   * This forces the creation of an instance for a given class name. If the
   * class provides a public default constructor, it is called. If the class has
   * a private default constructor, it is made accessible and then called.
   *
   * @param c a <code>Class</code> the class to instantiate
   * @return an <code>Object</code> which is an instance of the specified class
   */
  public Object forceInstance(Class c)
  {
	
    try
    {
      if (hasDefaultConstructor(c))
        return c.newInstance();
      else if (hasDefaultPrivateConstructor(c))
        return c.newInstance();
    }
    catch (InstantiationException ie) {}
    catch (IllegalAccessException iae) {}
    

    Objenesis objenesis = new ObjenesisStd();
    Object o = objenesis.newInstance(c);
    return o;
  }
}
