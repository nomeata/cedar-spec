forbid(
  principal is a in a::":6\u{11}\0\0333%:666",
  action == Action::"action",
  resource == a::":6\u{11}\0\0333%:666"
) when {
  true && (a::"" has "m_ss")
};
