permit(
  principal == a::":\0\u{11}\0\u{2}3333",
  action == Action::"action",
  resource
) when {
  true && (a::":\0\u{11}\0\u{2}3333" has "m_ss")
};
