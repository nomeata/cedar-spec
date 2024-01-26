forbid(
  principal is a in a::"%:666",
  action == Action::"action",
  resource in a::"%:666"
) when {
  true && (a::"" has "m_ss")
};
