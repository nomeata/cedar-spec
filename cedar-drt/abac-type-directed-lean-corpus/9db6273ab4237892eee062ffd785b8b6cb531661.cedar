permit(
  principal == a::"\0\0\066\u{13}6",
  action,
  resource is a in a::"\0\0\066\u{13}6"
) when {
  (true && (principal in action)) && false
};
