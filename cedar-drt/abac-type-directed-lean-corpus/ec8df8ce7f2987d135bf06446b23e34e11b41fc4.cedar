permit(
  principal == a::"        \u{11}\0\0\0\0\0id   \0 ",
  action in [Action::"action"],
  resource == a::"        \u{11}\0\0\0\0\0id   \0 "
) when {
  (true && (a::"        \u{11}\0\0\0\0\0id   \0 " has "                                           ")) && ((if ((decimal("231488583518862.6952")) == (decimal("231488553081845.3536"))) then (ip("                                           ")) else (ip("                                           "))).isMulticast())
};
