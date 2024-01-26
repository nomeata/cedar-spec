permit(
  principal == a::"",
  action,
  resource == a::"\0,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,626\u{1}"
) when {
  true && (principal is a)
};
