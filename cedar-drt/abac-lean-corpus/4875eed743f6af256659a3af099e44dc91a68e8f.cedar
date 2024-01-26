@_("iZZi\n}ZZZZ\u{16}RZZZZZZjjjjbjjjjjjjjjbjjjIIIIIIIIIIIIIIIIIIIIIIIIIIIIjjjjjjjii\u{10}\'\0\0\0\0\0\0\0\0\0\0\0\0\0\u{16}\0")
permit(
  principal,
  action,
  resource
) when {
  (true && (F::"" == (!(!action)))) && (!(!(!action)))
};
