package com.diffblue.java_testcase;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;
import java.util.Optional;

import org.objenesis.ObjenesisStd;

/**
 * Describe class <code>Reflector</code> here.
 *
 * @author Matthias Guedemann
 * @version 1.0
 */
public final class Reflector
{
  private Reflector() {}

  private static <T> void setInstanceField(Class<T> c, Object o, String fieldName, Object newVal) throws NoSuchFieldException, IllegalArgumentException
  {
    if (c == null) throw new NoSuchFieldException();
    Optional<Field> field = Arrays.stream(c.getDeclaredFields()).filter(f -> f.getName().equals(fieldName)).findAny();
    if (!field.isPresent()) setInstanceField(c.getSuperclass(), o, fieldName, newVal);
    else
    {
      Field property = field.get();
      property.setAccessible(true);
      try {
        property.set(o, newVal);
      } catch (IllegalAccessException e) {
        throw new RuntimeException(e); // Should never happen.
      }
    }
  }

  /**
   * Changes a given field of an object instance via reflection, bypassing the
   * private modifier.
   *
   * @param o an <code>Object</code> instance to change
   * @param fieldName a <code>String</code> the name of the field to change
   * @param newVal an <code>Object</code> the new value for the field
   * 
   * @throws NoSuchFieldException if a field with the specified name is not found.
   * @throws IllegalArgumentException if the specified object is not an instance of the class or interface declaring the underlying field (or a subclass or implementor thereof), or if an unwrapping conversion fails.
   */
  public static void setInstanceField(Object o, String fieldName, Object newVal) throws NoSuchFieldException, IllegalArgumentException
  {
    setInstanceField(o.getClass(), o, fieldName, newVal);
  }

  /**
   * This forces the creation of an instance for a given class name.
   *
   * @param className a <code>String</code> giving the name of the class
   * @return an <code>Object</code> which is an instance of the specified class
   * @throws ClassNotFoundException if the class cannot be found in the
   * classpath
   */
  public static Object forceInstance(String className) throws ClassNotFoundException
  {
    return forceInstance(Class.forName(className));
  }

  private static Optional<Constructor<?>> getDefaultConstructor(Class<?> c)
  {
    return Arrays.stream(c.getDeclaredConstructors()).filter(ctor -> ctor.getParameterCount() == 0).findAny();
  }

  /**
   * This forces the creation of an instance for a given class name. If the
   * class provides a public default constructor, it is called. If the class has
   * a private default constructor, it is made accessible and then called.
   *
   * @param c a <code>Class</code> the class to instantiate
   * @return an <code>Object</code> which is an instance of the specified class
   */
  @SuppressWarnings("unchecked")
  public static <T> T forceInstance(Class<T> c)
  {
    Optional<Constructor<?>> ctor = getDefaultConstructor(c);
    if (ctor.isPresent())
    {
      Constructor<?> defaultCtor = ctor.get();
      defaultCtor.setAccessible(true);
      try { return (T) defaultCtor.newInstance(); }
      catch (InstantiationException | InvocationTargetException | IllegalAccessException e) {}
    }
    return new ObjenesisStd().newInstance(c);
  }
}
