permit(
  principal == a::"ZZZZZZZZZZZZZZZZ\u{1a}Z\0\0\0\0\0\0\0\0\0j",
  action in [Action::"uuuuuuuuuuuuuuuuuuuuuu#jjjjjj",Action::"",Action::""],
  resource
) when {
  true && context
};
