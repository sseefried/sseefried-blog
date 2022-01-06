-- https://stackoverflow.com/questions/48169995/pandoc-how-to-link-to-a-section-in-another-markdown-file
function Link (link)
  link.target = link.target:gsub('(.+)%.md', '%1.html')
  return link
end
